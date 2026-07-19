{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}

-- | The node-shape rebuilder used when canonicalising e-nodes.
module Data.EGraph.Types.EGraph.Refill (refill) where

import Prelude

{- | A strict, allocation-lean applicative for redistributing a flat list of
values into the holes of a 'Traversable' shape, left to right.  Unlike base's
lazy 'Data.Traversable.mapAccumL' (whose @StateL@ applicative boxes a
@(state, value)@ pair per element), the remaining-list state is threaded through
an unboxed tuple, so the traversal fuses to a tight loop that allocates only the
result structure.

Kept in its own module because 'UnboxedTuples' and 'OverloadedLabels' clash in
the lexer (@(#label@ would parse as the unboxed-tuple opener), and the rest of
the e-graph code leans on overloaded labels.
-}
newtype Distribute a x = Distribute {runDistribute :: [a] -> (# [a], x #)}

instance Functor (Distribute a) where
  fmap f (Distribute g) = Distribute (\s -> case g s of (# s', x #) -> (# s', f x #))
  {-# INLINE fmap #-}

instance Applicative (Distribute a) where
  pure x = Distribute (\s -> (# s, x #))
  {-# INLINE pure #-}
  Distribute gf <*> Distribute gx =
    Distribute (\s -> case gf s of (# s', f #) -> case gx s' of (# s'', x #) -> (# s'', f x #))
  {-# INLINE (<*>) #-}

-- | Rebuild a shape from the list of its (transformed) children.
refill :: forall t a b. (Traversable t) => t b -> [a] -> t a
{-# INLINE refill #-}
refill shape vals =
  case runDistribute (traverse (\_ -> Distribute pop) shape) vals of
    (# _, r #) -> r
  where
    pop :: [a] -> (# [a], a #)
    pop (x : xs) = (# xs, x #)
    pop [] = error "refill: impossible: child count mismatch"
