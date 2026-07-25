{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.Relational (
  ematch,
  ematchDb,
  ematchDbWithCount,
  PreparedPatternQuery,
  prepare,
  ematchPreparedDbWithCount,
  query,
  genericJoin,
  compile,
) where

import Control.Functor.Linear qualified as Control
import Control.Lens (at, (%~), (&), (^.))
import Control.Monad.Borrow.Pure
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution (..))
import Data.EGraph.Types
import Data.FMList qualified as FML
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.Foldable1 (foldl1')
import Data.Functor qualified as Functor
import Data.Functor.Classes (Show1)
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Hashable (Hashable (..))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (catMaybes, fromMaybe)
import Data.Ord (Down (..))
import Data.Semigroup (Min (..), Sum (..))
import Data.Trie (project)
import Data.Trie qualified as Trie
import Data.Vector qualified as V
import GHC.Generics (Generic, Generically (..))
import Prelude.Linear qualified as PL

{-# INLINEABLE ematch #-}
ematch ::
  (Hashable v, Traversable l, HasDatabase l) =>
  Pattern l v ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur [(EClassId, Substitution v)])
ematch pat egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur db <- buildDatabase egraph
    Control.pure PL.$ Ur $ ematchDb (compile pat) db

{-# INLINEABLE ematchDb #-}
ematchDb ::
  (Hashable v, HasDatabase l) =>
  PatternQuery l v -> Database l -> [(EClassId, Substitution v)]
ematchDb pq@PatternQuery {..} db =
  map (fmap (materializeSubst varNames)) (fst (ematchDbWithCount pq db))

{- | Materialize the user-facing named substitution from an interned one —
byte-for-byte the former per-match build, now applied to dedup survivors
only, at the public boundary.
-}
materializeSubst :: (Hashable v) => V.Vector (Maybe v) -> IntSubst -> Substitution v
materializeSubst varNames sub =
  let !subs' =
        Substitution $
          V.ifoldl'
            ( \acc i mname -> case mname of
                Just name | Just eid <- IM.lookup i sub -> HM.insert name eid acc
                _ -> acc
            )
            HM.empty
            varNames
   in subs'

{-# INLINEABLE ematchDbWithCount #-}
ematchDbWithCount ::
  (HasDatabase l) =>
  PatternQuery l v -> Database l -> ([(EClassId, IntSubst)], Int)
ematchDbWithCount PatternQuery {..} db =
  (nubMatches HS.empty matches, rawSize)
  where
    subs = query patQuery db
    rawSize = sum (IM.size <$> subs)
    !vs = userVars varNames
    matches =
      map
        ( \sub ->
            let !rootId = IM.findWithDefault (error "ematchDb: root variable unbound") root sub
             in (rootId, sub)
        )
        subs

    nubMatches !_ [] = []
    nubMatches !seen (m@(rootId, sub) : rest)
      | HS.member key seen = nubMatches seen rest
      | otherwise = m : nubMatches (HS.insert key seen) rest
      where
        !key = MatchKey rootId vs sub

data PreparedAtom l = PreparedAtom
  { preparedAtom :: !(Atom l VarId)
  , preparedOperator :: !(Operator l)
  , preparedPositions :: !(IntMap (NonEmpty Int))
  }
  deriving (Generic)

deriving stock instance (Show1 l) => Show (PreparedAtom l)

data PreparedPatternQuery l v = PreparedPatternQuery
  { originalQuery :: !(PatternQuery l v)
  , preparedBody :: !(Maybe (NonEmpty (PreparedAtom l)))
  }
  deriving (Generic)

deriving stock instance (Show1 l, Show v) => Show (PreparedPatternQuery l v)

prepare :: (Functor l, Foldable l) => PatternQuery l v -> PreparedPatternQuery l v
prepare originalQuery@PatternQuery {patQuery} =
  PreparedPatternQuery
    { originalQuery
    , preparedBody = case patQuery of
        SelectAll {} -> Nothing
        Conj (_ ::- body) -> Just (prepareAtom <$> body)
    }
  where
    prepareAtom atom@(Atom MkRel {args}) =
      PreparedAtom
        { preparedAtom = atom
        , preparedOperator = toOperator args
        , preparedPositions =
            IM.fromListWith
              (flip (<>))
              [(v, NE.singleton i) | (i, v) <- zip [0 ..] (F.toList atom)]
        }

{-# INLINEABLE ematchPreparedDbWithCount #-}
ematchPreparedDbWithCount ::
  (HasDatabase l) =>
  PreparedPatternQuery l v -> Database l -> ([(EClassId, IntSubst)], Int)
ematchPreparedDbWithCount PreparedPatternQuery {originalQuery = PatternQuery {..}, ..} db =
  (nubMatches HS.empty matches, rawSize)
  where
    subs = case (patQuery, preparedBody) of
      (SelectAll v, Nothing) -> map (IM.singleton v) (selectAll db)
      (Conj cq, Just body) -> genericJoinPrepared cq body db
      _ -> error "ematchPreparedDbWithCount: inconsistent prepared query"
    rawSize = sum (IM.size <$> subs)
    !vs = userVars varNames
    matches =
      map
        ( \sub ->
            let !rootId = IM.findWithDefault (error "ematchDb: root variable unbound") root sub
             in (rootId, sub)
        )
        subs

    nubMatches !_ [] = []
    nubMatches !seen (m@(rootId, sub) : rest)
      | HS.member key seen = nubMatches seen rest
      | otherwise = m : nubMatches (HS.insert key seen) rest
      where
        !key = MatchKey rootId vs sub

{- | Dedup key: (root, interned substitution viewed at the named positions) —
the exact association content of the former (rootId, named 'Substitution')
key, with no projected map materialized (node compares happen inside the
'HashSet' probes only). INVARIANTS: (1) sound only for 'varNames' with at
most one id per name — all 'compile' output; hand-built or fmap'd
'PatternQuery's with duplicate names are out of spec; (2) 'Eq' walks the
LEFT key's position list, so the instances are lawful only among keys of a
single 'ematchDbWithCount' call — the seen-set is call-local and this type
is module-private, so keys never cross calls.
-}
data MatchKey = MatchKey !EClassId [VarId] !IntSubst

instance Eq MatchKey where
  MatchKey r1 vs s1 == MatchKey r2 _ s2 =
    r1 == r2 && all (\v -> IM.lookup v s1 == IM.lookup v s2) vs
  {-# INLINE (==) #-}

instance Hashable MatchKey where
  hashWithSalt salt (MatchKey r vs s) =
    F.foldl' (\ !acc v -> hashWithSalt acc (IM.lookup v s)) (hashWithSalt salt r) vs
  {-# INLINE hashWithSalt #-}

{-# INLINEABLE query #-}
query ::
  forall l.
  (HasDatabase l) =>
  Query l VarId ->
  Database l ->
  [IntSubst]
query (Conj cq) = genericJoin cq
query (SelectAll v) = map (IM.singleton v) . selectAll

data RelationState l = RelationState
  { database :: !Trie.Trie
  , positions :: !(IntMap (NonEmpty Int))
  }
  deriving (Show, Generic)

data VarWeight = VarWeight
  { numRels :: !(Down (Sum Word))
  , smallestDbSize :: !(Min Word)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via Generically VarWeight

buildQueryState ::
  (HasDatabase l) =>
  Database l ->
  Atom l VarId ->
  Maybe (RelationState l, IntMap VarWeight)
buildQueryState db atom@(Atom MkRel {args}) = do
  !database <- db ^. at (toOperator args)
  -- Column positions of each variable. At compile time every column is a
  -- 'QVar', so traversal order equals row-column order (id : children).
  let !positions =
        IM.fromListWith (flip (<>)) [(v, NE.singleton i) | (i, v) <- zip [0 ..] (F.toList atom)]
      weight =
        VarWeight
          { numRels = Down (Sum 1)
          , smallestDbSize = Min (Trie.size database)
          }
      !stats = IM.map (const weight) positions
  pure (RelationState {..}, stats)

buildPreparedQueryState ::
  (HasDatabase l) =>
  Database l ->
  PreparedAtom l ->
  Maybe (RelationState l, IntMap VarWeight)
buildPreparedQueryState db PreparedAtom {..} = do
  !database <- db ^. at preparedOperator
  let weight =
        VarWeight
          { numRels = Down (Sum 1)
          , smallestDbSize = Min (Trie.size database)
          }
      !stats = IM.map (const weight) preparedPositions
  pure (RelationState {positions = preparedPositions, ..}, stats)

{-# INLINEABLE genericJoin #-}
genericJoin ::
  forall l.
  (HasDatabase l) =>
  ConjunctiveQuery l VarId ->
  Database l ->
  [IntSubst]
genericJoin (hd ::- (atm@(Atom rel@MkRel {args}) :| [])) db = fromMaybe [] do
  let vars = IS.fromList (F.toList atm)
      frees :: [IntSubst]
      frees =
        filter (not . IM.null) $
          sequenceA $
            IM.fromSet (const $ map Trie.fromKey $ IS.toList $ universe db) $
              IS.fromList hd `IS.difference` vars
  trie <- db ^. at (toOperator args)
  let !matches = Trie.match (F.toList rel) trie
  pure $
    if null frees
      then matches
      else IM.union <$> matches <*> frees
genericJoin (hd ::- qs) db = fromMaybe [] do
  relsStats <- mapM (buildQueryState db) qs
  let rels = fst <$> relsStats
      varStat =
        IM.unionWith
          (<>)
          (foldl1' (IM.unionWith (<>)) (snd <$> relsStats))
          (IM.fromList (map (,VarWeight {numRels = 0, smallestDbSize = maxBound}) hd))
      -- Eliminate variables occurring in the most relations first, using
      -- the smallest participating relation as the tie-break. This is the
      -- same cost model intended by hegg, represented directly instead of
      -- routing a cost-sorted list through IntSet.fromAscList (whose input
      -- contract requires id order and is not satisfied by a cost order).
      order = map fst $ sortOn snd $ IM.toList varStat
  -- NB: @go@ accumulates in 'FML.FMList', whose @(<>)@ is O(1); accumulating in a
  -- plain list here would be a left-nested @(++)@ (via @foldMap'@) and hence O(N^2)
  -- in the number of matches. Materialise to a list exactly once, at the boundary.
  pure $ FML.toList (go order rels IM.empty)
  where
    -- TODO: consider some selection strategy
    go [] !_qs sub = FML.singleton sub
    go (v : vs) !qs sub =
      let (!doms, !qs') =
            Functor.unzip $
              fmap
                ( \q ->
                    case IM.lookup v q.positions of
                      Nothing -> (Nothing, const q)
                      Just poss ->
                        ( Just $ project poss q.database
                        , \eid ->
                            q
                              & #database %~ Trie.focus ((,eid) <$> poss)
                        )
                )
                qs
          !domain = case catMaybes (NE.toList doms) of
            [] -> universe db
            d : ds -> intersectAll d ds
       in foldMap'
            ( \k ->
                let !eid = Trie.fromKey k
                 in go vs (($ eid) <$> qs') (IM.insert v eid sub)
            )
            (IS.toList domain)

    intersectAll :: IS.IntSet -> [IS.IntSet] -> IS.IntSet
    intersectAll !acc ds
      | IS.null acc = IS.empty
      | otherwise = case ds of
          [] -> acc
          d : rest -> intersectAll (IS.intersection acc d) rest

genericJoinPrepared ::
  forall l.
  (HasDatabase l) =>
  ConjunctiveQuery l VarId ->
  NonEmpty (PreparedAtom l) ->
  Database l ->
  [IntSubst]
genericJoinPrepared (hd ::- _) (PreparedAtom {preparedAtom = atom@(Atom rel), preparedOperator} :| []) db = fromMaybe [] do
  let vars = IS.fromList (F.toList atom)
      frees :: [IntSubst]
      frees =
        filter (not . IM.null) $
          sequenceA $
            IM.fromSet (const $ map Trie.fromKey $ IS.toList $ universe db) $
              IS.fromList hd `IS.difference` vars
  trie <- db ^. at preparedOperator
  let !matches = Trie.match (F.toList rel) trie
  pure $ if null frees then matches else IM.union <$> matches <*> frees
genericJoinPrepared (hd ::- _) qs db = fromMaybe [] do
  relsStats <- mapM (buildPreparedQueryState db) qs
  let rels = fst <$> relsStats
      varStat =
        IM.unionWith
          (<>)
          (foldl1' (IM.unionWith (<>)) (snd <$> relsStats))
          (IM.fromList (map (,VarWeight {numRels = 0, smallestDbSize = maxBound}) hd))
      order = map fst $ sortOn snd $ IM.toList varStat
  pure $ FML.toList (go order rels IM.empty)
  where
    go [] !_qs sub = FML.singleton sub
    go (v : vs) !qs' sub =
      let (!doms, !qs'') =
            Functor.unzip $
              fmap
                ( \q ->
                    case IM.lookup v q.positions of
                      Nothing -> (Nothing, const q)
                      Just poss ->
                        ( Just $ project poss q.database
                        , \eid -> q & #database %~ Trie.focus ((,eid) <$> poss)
                        )
                )
                qs'
          !domain = case catMaybes (NE.toList doms) of
            [] -> universe db
            d : ds -> intersectAllPrepared d ds
       in foldMap'
            ( \k ->
                let !eid = Trie.fromKey k
                 in go vs (($ eid) <$> qs'') (IM.insert v eid sub)
            )
            (IS.toList domain)

    intersectAllPrepared !acc ds
      | IS.null acc = IS.empty
      | otherwise = case ds of
          [] -> acc
          d : rest -> intersectAllPrepared (IS.intersection acc d) rest
