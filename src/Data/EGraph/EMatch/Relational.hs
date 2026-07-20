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
  query,
  genericJoin,
  compile,
) where

import Control.Functor.Linear qualified as Control
import Control.Lens (at, (%~), (&), (^.))
import Control.Monad.Borrow.Pure
import Data.Bifunctor qualified as Bi
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution (..))
import Data.EGraph.Types
import Data.FMList qualified as FML
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.Foldable1 (foldl1')
import Data.Function (on)
import Data.Functor qualified as Functor
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (sortBy, sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (catMaybes, fromMaybe)
import Data.Trie (project)
import Data.Trie qualified as Trie
import Data.Vector qualified as V
import GHC.Generics (Generic)
import Prelude.Linear qualified as PL

{- | Internal substitution over interned 'VarId's; translated back to the
user-facing 'Substitution' only at the 'ematchDb' boundary.
-}
type IntSubst = IntMap EClassId

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
ematchDb pat db = nubMatches HS.empty (fst $ ematchDbWithCount pat db)
  where
    nubMatches !_ [] = []
    nubMatches !seen (match : rest)
      | HS.member match seen = nubMatches seen rest
      | otherwise = match : nubMatches (HS.insert match seen) rest

{-# INLINEABLE ematchDbWithCount #-}
ematchDbWithCount ::
  (Hashable v, HasDatabase l) =>
  PatternQuery l v -> Database l -> ([(EClassId, Substitution v)], Int)
ematchDbWithCount PatternQuery {..} db =
  ( map
      ( \sub ->
          let !rootId = IM.findWithDefault (error "ematchDb: root variable unbound") root sub
              !subs' =
                Substitution $
                  V.ifoldl'
                    ( \acc i mname -> case mname of
                        Just name | Just eid <- IM.lookup i sub -> HM.insert name eid acc
                        _ -> acc
                    )
                    HM.empty
                    varNames
           in (rootId, subs')
      )
      subs
  , rawSize
  )
  where
    subs = query patQuery db
    rawSize = sum (IM.size <$> subs)

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
  { atom :: !(Atom l VarId)
  , database :: !Trie.Trie
  , positions :: !(IntMap (NonEmpty Int))
  }
  deriving (Show, Generic)

buildQueryState ::
  (HasDatabase l) =>
  Database l ->
  Atom l VarId ->
  Maybe (RelationState l)
buildQueryState db atom@(Atom MkRel {args}) = do
  !database <- db ^. at (toOperator args)
  -- Column positions of each variable. At compile time every column is a
  -- 'QVar', so traversal order equals row-column order (id : children).
  let !positions =
        IM.fromListWith (flip (<>)) [(v, NE.singleton i) | (i, v) <- zip [0 ..] (F.toList atom)]
  pure RelationState {..}

{-# INLINEABLE genericJoin #-}
genericJoin ::
  forall l.
  (HasDatabase l) =>
  ConjunctiveQuery l VarId ->
  Database l ->
  [IntSubst]
genericJoin (_hd ::- qs) db = fromMaybe [] do
  rels <- mapM (buildQueryState db) qs
  let
    -- Keep hegg's variable ordering exactly.  In particular, its
    -- @fromAscList@ is applied after sorting by cost rather than by id;
    -- repeated variables can therefore survive and produce duplicate
    -- substitutions.  Those multiplicities are observable because the
    -- backoff scheduler sums substitution sizes.
    occurrences =
      foldl (\acc atm -> F.toList atm <> acc) [] qs
    vars = occurrences
    atomLength = F.length
    varCost v =
      foldl
        (\acc atm -> if v `elem` F.toList atm then acc - 100 + atomLength atm else acc)
        0
        qs
    order = IS.toList $ IS.fromAscList $ sortBy (compare `on` varCost) vars
  -- NB: @go@ accumulates in 'FML.FMList', whose @(<>)@ is O(1); accumulating in a
  -- plain list here would be a left-nested @(++)@ (via @foldMap'@) and hence O(N^2)
  -- in the number of matches. Materialise to a list exactly once, at the boundary.
  pure $ FML.toList (go order rels IM.empty)
  where
    -- TODO: consider some selection strategy
    go [] !qs sub = foldMap' (const (FML.singleton sub)) qs
    go (v : vs) !qs sub =
      let (!doms, !qs') =
            Bi.first (sortOn IS.size . catMaybes . NE.toList) $
              Functor.unzip $
                fmap
                  ( \q ->
                      case IM.lookup v q.positions of
                        Nothing -> (Nothing, const q)
                        Just poss ->
                          ( Just $ project poss q.database
                          , \eid ->
                              q
                                & #atom %~ substAtom v eid
                                & #database %~ Trie.focus ((,eid) <$> poss)
                          )
                  )
                  qs
          !domain = case NE.nonEmpty doms of
            Nothing -> universe db
            Just xs' -> foldl1' IS.intersection xs'
       in foldMap'
            ( \k ->
                let !eid = Trie.fromKey k
                 in go vs (($ eid) <$> qs') (IM.insert v eid sub)
            )
            (IS.toList domain)
