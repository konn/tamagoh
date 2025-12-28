{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
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
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.Foldable1 (foldl1')
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (mapMaybe)
import Data.Trie (project)
import Data.Unrestricted.Linear (Ur (..))
import Prelude.Linear qualified as PL

ematch ::
  (Hashable v, Traversable l, HasDatabase l, Movable1 l) =>
  Pattern l v -> Borrow k α (EGraph l) %1 -> BO α (Ur [Substitution v])
ematch pat egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur db <- buildDatabase egraph
    Control.pure PL.$ Ur $ ematchDb pat db

ematchDb ::
  (Hashable v, Traversable l, HasDatabase l) =>
  Pattern l v -> Database l -> [Substitution v]
ematchDb pat db =
  map
    ( mapMaybeVar \case
        PVar v -> Just v
        _ -> Nothing
    )
    $ query (compile pat) db

nubHash :: (Hashable a) => [a] -> [a]
nubHash = go mempty
  where
    go !_ [] = []
    go !s (x : xs)
      | HS.member x s = go s xs
      | otherwise = x : go (HS.insert x s) xs

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
genericJoin (hd :- qs) db = go (nubHash hd) mempty
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
