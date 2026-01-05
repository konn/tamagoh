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
  query,
  genericJoin,
  compile,
) where

import Control.Foldl qualified as L
import Control.Functor.Linear qualified as Control
import Control.Lens (at, folded, indexing, withIndex, (%~), (&), (^.))
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Utils (nubHash)
import Data.Bifunctor qualified as Bi
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.Foldable1 (foldl1')
import Data.Functor qualified as Functor
import Data.Functor.Classes (Show1)
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Product (Product (..))
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (catMaybes, fromMaybe)
import Data.Trie (project)
import Data.Trie qualified as Trie
import Data.Tuple qualified as Tuple
import Data.Unrestricted.Linear (Ur (..))
import Data.Unrestricted.Linear.Lifted (Movable1)
import GHC.Generics (Generic)
import Prelude.Linear qualified as PL

ematch ::
  (Hashable v, Show v, Show1 l, Traversable l, HasDatabase l, Movable1 l) =>
  Pattern l v ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur [(EClassId, Substitution v)])
ematch pat egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur db <- buildDatabase egraph
    Control.pure PL.$ Ur $ ematchDb (compile pat) db

ematchDb ::
  (Hashable v, Show v, Show1 l, HasDatabase l) =>
  PatternQuery l v -> Database l -> [(EClassId, Substitution v)]
ematchDb PatternQuery {..} db =
  map
    ( \subs ->
        let subs' = mapMaybeVar \case { PVar v -> Just v; _ -> Nothing } subs
            rootId = fromMaybe (error $ "ematchDB: var not found: " <> show (patQuery, root, subs)) $ lookupVar root subs
         in (rootId, subs')
    )
    $ query patQuery db

query ::
  forall l v.
  (Hashable v, HasDatabase l) =>
  Query l v ->
  Database l ->
  [Substitution v]
query (Conj cq) = genericJoin cq
query (SelectAll v) = map (singletonVar v) . HS.toList . universe

data RelationState l v = RelationState
  { atom :: !(Atom l v)
  , database :: !Trie.Trie
  , positions :: !(HM.HashMap v (NonEmpty Int))
  }
  deriving (Show, Eq, Ord, Generic)

buildQueryState ::
  (HasDatabase l, Hashable v) =>
  Database l -> Atom l v -> Maybe (RelationState l v)
buildQueryState db atom@(Atom MkRel {args}) = do
  !database <- db ^. at (toOperator args)
  let !positions = L.foldOver (indexing folded . withIndex) (L.premap Tuple.swap $ L.foldByKeyHashMap $ NE.fromList <$> L.list) atom
  pure RelationState {..}

genericJoin ::
  forall l v.
  (Hashable v, HasDatabase l) =>
  ConjunctiveQuery l v ->
  Database l ->
  [Substitution v]
genericJoin (hd :- qs) db = fromMaybe [] do
  rels <- mapM (buildQueryState db) qs
  pure $ go (nubHash $ F.toList $ Pair hd (Compose qs)) rels mempty
  where
    -- TODO: consider some selection strategy
    go :: [v] -> NonEmpty (RelationState l v) -> Substitution v -> [Substitution v]
    go [] !_ sub = [sub]
    go (v : vs) qs sub =
      let
       in -- !() = DT.trace ("Substituting " <> show v <> " in query: " <> show qs <> " with subs" <> show sub) ()
          let (!doms, !qs') =
                Bi.first (sortOn HS.size . catMaybes . NE.toList) $
                  Functor.unzip $
                    fmap
                      ( \q ->
                          case HM.lookup v q.positions of
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
                Just xs' -> foldl1' HS.intersection xs'
           in -- !() = DT.trace ("    Domain for " <> show v <> ": " <> show domain) ()
              foldMap' (\eid -> go vs (($ eid) <$> qs') (insertVar v eid sub)) domain
