module Data.EGraph.EMatch.Relational (genericJoin) where

import Data.EGraph.EMatch.Relational.Build
import Data.EGraph.EMatch.Relational.Types
import Data.EGraph.EMatch.Types
import Data.Foldable1 (foldl1')
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (mapMaybe)
import Data.Trie (project)

nubHash :: (Hashable a) => [a] -> [a]
nubHash = go mempty
  where
    go !_ [] = []
    go !s (x : xs)
      | HS.member x s = go s xs
      | otherwise = x : go (HS.insert x s) xs

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
