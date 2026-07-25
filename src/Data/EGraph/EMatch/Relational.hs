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
  preparedLayoutEligible,
  preparedStaticOrder,
  preparedRuntimeOrder,
  preparedOperators,
  preparedDatabaseRequirements,
  ematchPreparedDbWithCount,
  query,
  genericJoin,
  compile,
) where

import Control.Functor.Linear qualified as Control
import Control.Lens (at, (^.))
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
  , preparedVariables :: !(Maybe [VarId])
  }
  deriving (Generic)

deriving stock instance (Show1 l) => Show (PreparedAtom l)

data PreparedLayoutAtom l = PreparedLayoutAtom
  { layoutAtom :: !(PreparedAtom l)
  , layoutIndex :: !(Maybe (PreparedIndexKey l))
  , layoutPositions :: !(IntMap (NonEmpty Int))
  }
  deriving (Generic)

deriving stock instance (Show1 l) => Show (PreparedLayoutAtom l)

data PreparedLayoutPlan l = PreparedLayoutPlan
  { layoutOrder :: ![VarId]
  , layoutAtoms :: !(NonEmpty (PreparedLayoutAtom l))
  }
  deriving (Generic)

deriving stock instance (Show1 l) => Show (PreparedLayoutPlan l)

data PreparedPatternQuery l v = PreparedPatternQuery
  { originalQuery :: !(PatternQuery l v)
  , preparedBody :: !(Maybe (NonEmpty (PreparedAtom l)))
  , preparedLayoutPlan :: !(Maybe (PreparedLayoutPlan l))
  }
  deriving (Generic)

deriving stock instance (Show1 l, Show v) => Show (PreparedPatternQuery l v)

prepare :: (Functor l, Foldable l) => PatternQuery l v -> PreparedPatternQuery l v
prepare originalQuery@PatternQuery {patQuery} =
  PreparedPatternQuery
    { originalQuery
    , preparedBody
    , preparedLayoutPlan
    }
  where
    preparedBody = case patQuery of
      SelectAll {} -> Nothing
      Conj (_ ::- body) -> Just (prepareAtom <$> body)

    preparedLayoutPlan = case (patQuery, preparedBody) of
      (Conj (headVars ::- _), Just body)
        | all (maybe False (const True) . preparedVariables) body
        , IS.fromList headVars
            `IS.isSubsetOf` F.foldMap (IM.keysSet . preparedPositions) body
        , NE.length body >= 3 || isDirectedUnaryChain body ->
            let !order = staticVariableOrder headVars body
             in do
                  atoms <- traverse (prepareLayoutAtom order) body
                  if NE.length body >= 3 || any hasPreparedIndex atoms
                    then Just (PreparedLayoutPlan order atoms)
                    else Nothing
      _ -> Nothing

    prepareAtom atom@(Atom rel@MkRel {args}) =
      PreparedAtom
        { preparedAtom = atom
        , preparedOperator = toOperator args
        , preparedPositions =
            IM.fromListWith
              (flip (<>))
              [(v, NE.singleton i) | (i, v) <- zip [0 ..] (F.toList atom)]
        , preparedVariables =
            traverse
              ( \case
                  QVar v -> Just v
                  EId _ -> Nothing
              )
              (F.toList rel)
        }

    prepareLayoutAtom order atom@PreparedAtom {preparedVariables = Just variables, ..} = do
      let !layoutColumns =
            F.foldMap
              (\v -> maybe [] F.toList (IM.lookup v preparedPositions))
              order
      layout <- mkColumnLayout (length variables) layoutColumns
      permutedVariables <- permuteColumns layout variables
      let !positions =
            IM.fromListWith
              (flip (<>))
              [(v, NE.singleton i) | (i, v) <- zip [0 ..] permutedVariables]
      index <-
        if layout == identityColumnLayout (length variables)
          then Just Nothing
          else Just <$> mkPreparedIndexKey preparedOperator layout
      pure
        PreparedLayoutAtom
          { layoutAtom = atom
          , layoutIndex = index
          , layoutPositions = positions
          }
    prepareLayoutAtom _ PreparedAtom {preparedVariables = Nothing} = Nothing

    hasPreparedIndex PreparedLayoutAtom {layoutIndex = Just _} = True
    hasPreparedIndex PreparedLayoutAtom {layoutIndex = Nothing} = False

    isDirectedUnaryChain body = case NE.toList body of
      [left, right] -> case (preparedVariables left, preparedVariables right) of
        (Just [leftRoot, leftChild], Just [rightRoot, rightChild]) ->
          leftRoot /= leftChild
            && rightRoot /= rightChild
            && IS.size
              ( IS.intersection
                  (IS.fromList [leftRoot, leftChild])
                  (IS.fromList [rightRoot, rightChild])
              )
              == 1
            && (leftChild == rightRoot || rightChild == leftRoot)
        _ -> False
      _ -> False

preparedLayoutEligible :: PreparedPatternQuery l v -> Bool
preparedLayoutEligible PreparedPatternQuery {preparedLayoutPlan} =
  maybe False (const True) preparedLayoutPlan

preparedStaticOrder :: PreparedPatternQuery l v -> Maybe [VarId]
preparedStaticOrder PreparedPatternQuery {preparedLayoutPlan} =
  layoutOrder <$> preparedLayoutPlan

preparedRuntimeOrder ::
  (HasDatabase l) =>
  PreparedPatternQuery l v ->
  Database l ->
  Maybe [VarId]
preparedRuntimeOrder PreparedPatternQuery {originalQuery = PatternQuery {patQuery}, preparedBody} db =
  case (patQuery, preparedBody) of
    (Conj (headVars ::- _), Just body) -> do
      relsStats <- mapM (buildPreparedQueryState db) body
      let varStat =
            IM.unionWith
              (<>)
              (foldl1' (IM.unionWith (<>)) (snd <$> relsStats))
              (IM.fromList (map (,VarWeight {numRels = 0, smallestDbSize = maxBound}) headVars))
      pure $ map fst $ sortOn snd $ IM.toList varStat
    _ -> Nothing

staticVariableOrder :: [VarId] -> NonEmpty (PreparedAtom l) -> [VarId]
staticVariableOrder headVars atoms =
  map fst $ sortOn snd $ IM.toList varStat
  where
    zeroSizeWeight =
      VarWeight
        { numRels = Down (Sum 1)
        , smallestDbSize = Min 0
        }
    varStat =
      IM.unionWith
        (<>)
        (foldl1' (IM.unionWith (<>)) (IM.map (const zeroSizeWeight) . preparedPositions <$> atoms))
        (IM.fromList (map (,VarWeight {numRels = 0, smallestDbSize = maxBound}) headVars))

{- | Operators whose relation tries are needed to run a prepared query.

Variable-only queries return no operators because they use the database's
'selectAll' index instead.
-}
{-# INLINE preparedOperators #-}
preparedOperators :: PreparedPatternQuery l v -> [Operator l]
preparedOperators PreparedPatternQuery {preparedBody} =
  maybe [] (map preparedOperator . NE.toList) preparedBody

preparedDatabaseRequirements ::
  PreparedPatternQuery l v ->
  ([Operator l], [PreparedIndexKey l])
preparedDatabaseRequirements PreparedPatternQuery {preparedBody, preparedLayoutPlan} =
  case preparedLayoutPlan of
    Nothing -> (maybe [] (map preparedOperator . NE.toList) preparedBody, [])
    Just PreparedLayoutPlan {layoutAtoms} ->
      foldr
        ( \PreparedLayoutAtom {layoutAtom = PreparedAtom {preparedOperator}, layoutIndex} (operators, indexes) ->
            case layoutIndex of
              Nothing -> (preparedOperator : operators, indexes)
              Just index -> (operators, index : indexes)
        )
        ([], [])
        layoutAtoms

{-# INLINEABLE ematchPreparedDbWithCount #-}
ematchPreparedDbWithCount ::
  (HasDatabase l) =>
  PreparedPatternQuery l v -> Database l -> ([(EClassId, IntSubst)], Int)
ematchPreparedDbWithCount PreparedPatternQuery {originalQuery = PatternQuery {..}, ..} db =
  (nubMatches HS.empty matches, rawSize)
  where
    subs = case (patQuery, preparedBody) of
      (SelectAll v, Nothing) -> map (IM.singleton v) (selectAll db)
      (Conj cq, Just body) ->
        genericJoinPrepared preparedLayoutPlan cq body db
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
  , constraints :: !(IntMap EClassId)
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
  pure (RelationState {constraints = IM.empty, ..}, stats)

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
  pure (RelationState {positions = preparedPositions, constraints = IM.empty, ..}, stats)

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
  pure $ runGenericJoin db order rels

genericJoinPrepared ::
  forall l.
  (HasDatabase l) =>
  Maybe (PreparedLayoutPlan l) ->
  ConjunctiveQuery l VarId ->
  NonEmpty (PreparedAtom l) ->
  Database l ->
  [IntSubst]
genericJoinPrepared _ (hd ::- _) (PreparedAtom {preparedAtom = atom@(Atom rel), preparedOperator} :| []) db = fromMaybe [] do
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
genericJoinPrepared layoutPlan (hd ::- _) qs db =
  case layoutPlan >>= resolvePreparedLayoutPlan db of
    Just (order, rels) -> runGenericJoin db order rels
    Nothing -> fromMaybe [] do
      relsStats <- mapM (buildPreparedQueryState db) qs
      let rels = fst <$> relsStats
          varStat =
            IM.unionWith
              (<>)
              (foldl1' (IM.unionWith (<>)) (snd <$> relsStats))
              (IM.fromList (map (,VarWeight {numRels = 0, smallestDbSize = maxBound}) hd))
          order = map fst $ sortOn snd $ IM.toList varStat
      pure $ runGenericJoin db order rels

resolvePreparedLayoutPlan ::
  (HasDatabase l) =>
  Database l ->
  PreparedLayoutPlan l ->
  Maybe ([VarId], NonEmpty (RelationState l))
resolvePreparedLayoutPlan db PreparedLayoutPlan {layoutOrder, layoutAtoms} =
  (layoutOrder,) <$> traverse resolveAtom layoutAtoms
  where
    resolveAtom PreparedLayoutAtom {layoutAtom = PreparedAtom {preparedOperator}, ..} = do
      database <- case layoutIndex of
        Nothing -> db ^. at preparedOperator
        Just index -> getPreparedTrie index db
      pure
        RelationState
          { database
          , positions = layoutPositions
          , constraints = IM.empty
          }

runGenericJoin :: Database l -> [VarId] -> NonEmpty (RelationState l) -> [IntSubst]
runGenericJoin db order rels = FML.toList (go order rels IM.empty)
  where
    -- NB: @go@ accumulates in 'FML.FMList', whose @(<>)@ is O(1);
    -- materialise to a list exactly once, at the boundary.
    go [] !_qs sub = FML.singleton sub
    go (v : vs) !qs sub =
      let (!doms, !updateRelations) =
            Functor.unzip $
              fmap
                ( \q ->
                    case IM.lookup v q.positions of
                      Nothing -> (Nothing, const q)
                      Just poss ->
                        ( Just $ Trie.projectWithConstraints q.constraints poss q.database
                        , \eid ->
                            q
                              { constraints =
                                  F.foldl'
                                    (\acc column -> IM.insert column eid acc)
                                    q.constraints
                                    poss
                              }
                        )
                )
                qs
          !domain = case catMaybes (NE.toList doms) of
            [] -> universe db
            d : ds -> intersectAll d ds
       in foldMap'
            ( \k ->
                let !eid = Trie.fromKey k
                 in go vs (($ eid) <$> updateRelations) (IM.insert v eid sub)
            )
            (IS.toList domain)

    intersectAll !acc ds
      | IS.null acc = IS.empty
      | otherwise = case ds of
          [] -> acc
          d : rest -> intersectAll (IS.intersection acc d) rest
