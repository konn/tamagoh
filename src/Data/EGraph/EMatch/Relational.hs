{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
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

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Utils (nubHash)
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Foldable1 (foldl1')
import Data.Functor.Classes (Show1)
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Product (Product (..))
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Trie (project)
import Data.Unrestricted.Linear (Ur (..))
import Data.Unrestricted.Linear.Lifted (Movable1)
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
  (Hashable v, Show v, Show1 l, Traversable l, HasDatabase l) =>
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
  (Hashable v, Foldable l, HasDatabase l) =>
  Query l v ->
  Database l ->
  [Substitution v]
query (Conj cq) = genericJoin cq
query (SelectAll v) = map (singletonVar v) . HS.toList . universe

genericJoin ::
  forall l v.
  (Hashable v, Foldable l, HasDatabase l) =>
  ConjunctiveQuery l v ->
  Database l ->
  [Substitution v]
genericJoin (hd :- qs) db = go (nubHash $ F.toList $ Pair hd (Compose qs)) mempty
  where
    -- TODO: consider some selection strategy
    go :: [v] -> Substitution v -> [Substitution v]
    go [] sub = [sub]
    go (v : vs) sub =
      let atms = mapMaybe (\atm -> (atm,) <$> findVars v atm) $ NE.toList qs
          domain = case NE.nonEmpty atms of
            Nothing -> universe db
            Just xs' ->
              foldl1' HS.intersection $
                NE.map
                  (\(Atom (MkRel _ node), poss) -> project poss (getTrie node db))
                  xs'
       in concatMap (\eid -> go vs $ insertVar v eid sub) domain
