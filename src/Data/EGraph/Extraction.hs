{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Post-hoc extraction over a frozen e-graph: compute, per canonical
e-class, the minimum-cost e-node by fixpoint relaxation, then rebuild the
best term by recursive descent.

This mirrors the reference implementations — egg's @Extractor@
(@find_costs@ in @src\/extract.rs@) and hegg's @Data.Equality.Extraction@:
relaxation passes repeat until no class's best cost changes; within a pass
classes are visited in ascending canonical-id order and a class's nodes in
'Ord' order, and a class entry is updated only on a /strict/ cost decrease,
so the earliest witness in that order wins ties. The extracted result is
therefore deterministic and never depends on hash-iteration order.

Unlike the incremental 'Data.EGraph.Saturation.ExtractBest' analysis,
nothing here runs during saturation — this is the egg-faithful pipeline of
/saturate first, extract once at the end/.
-}
module Data.EGraph.Extraction (
  ClassNodes,
  classKey,
  findCosts,
  reconstruct,
) where

import Data.EGraph.Saturation (CostModel (..))
import Data.EGraph.Types (EClassId (..), ENode (..), Term, wrapTerm)
import Data.Functor.Classes (Ord1)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Semigroup (Min (..))
import Data.UnionFind.Linear (Key (..))

{- | Snapshot of the frozen e-graph: canonical class id ↦ its e-nodes.
Children must already be canonical ids and each node list sorted by 'Ord'
for the determinism guarantees documented in the module header.
-}
type ClassNodes l = IntMap [ENode l]

-- | The dense 'Int' behind an 'EClassId', for keying 'IntMap's.
classKey :: EClassId -> Int
classKey (EClassId (Key w)) = fromIntegral w

{- | Fixpoint cost relaxation (egg's @Extractor::find_costs@, hegg's
@findCosts@): repeatedly relax every class from its nodes whose children
already have costs, updating only on strict decrease, until stable.

The result is the unique least fixpoint provided 'costFunction' is
monotone in each child cost (egg's documented @CostFunction@ contract).
-}
findCosts ::
  forall cost l.
  (Traversable l, Ord1 l, CostModel cost l) =>
  ClassNodes l ->
  IntMap (cost, ENode l)
findCosts classes = go IntMap.empty
  where
    go :: IntMap (cost, ENode l) -> IntMap (cost, ENode l)
    go costs = case IntMap.foldlWithKey' step (False, costs) classes of
      (True, costs') -> go costs'
      (False, costs') -> costs'

    step :: (Bool, IntMap (cost, ENode l)) -> Int -> [ENode l] -> (Bool, IntMap (cost, ENode l))
    step (!changed, !acc) k nodes = case classBest acc nodes of
      Nothing -> (changed, acc)
      Just best@(!c, _) -> case IntMap.lookup k acc of
        Just (c0, _)
          | c < c0 -> (True, IntMap.insert k best acc)
          | otherwise -> (changed, acc)
        Nothing -> (True, IntMap.insert k best acc)

    -- The Ord-least node among the minimal-cost costable ones — identical to
    -- picking the first minimum of an Ord-sorted list (hegg's Set fold with
    -- 'min'), but without materializing and sorting the list: node
    -- comparisons happen only on exact cost ties.
    classBest :: IntMap (cost, ENode l) -> [ENode l] -> Maybe (cost, ENode l)
    classBest acc = foldl' pick Nothing
      where
        pick best node = case nodeCost acc node of
          Nothing -> best
          Just c -> case best of
            Just (cb, nb)
              | cb < c -> best
              | cb == c, nb <= node -> best
            _ -> Just (c, node)

    nodeCost :: IntMap (cost, ENode l) -> ENode l -> Maybe cost
    nodeCost acc (ENode node) = do
      children <- traverse (\cid -> Min . fst <$> IntMap.lookup (classKey cid) acc) node
      let Min c = costFunction children
      pure c

{- | Rebuild the best term from a 'findCosts' result by recursive descent
through each class's winning node (egg's @Extractor::find_best@).

Terminates on cyclic e-graphs provided the cost model is monotone: the
winner of a class then costs strictly more than any of its child classes'
minima, so the descent strictly decreases.
-}
reconstruct ::
  (Traversable l) =>
  IntMap (cost, ENode l) ->
  EClassId ->
  Maybe (Term l, cost)
reconstruct costs = go
  where
    go cid = do
      (c, ENode node) <- IntMap.lookup (classKey cid) costs
      term <- traverse (fmap fst . go) node
      pure (wrapTerm term, c)
