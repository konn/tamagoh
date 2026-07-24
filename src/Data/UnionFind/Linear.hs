{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- | Efficient union-find data structure using linear types for safe mutation
and raw unboxed arrays for performance. Read-path lookups ('find',
'unsafeFind') do NOT path-compress — union-by-rank keeps the trees shallow,
and writing through the borrow boundary on every lookup measurably loses
(TUNE-PLAN P9.14); the compressing variants remain as 'findMut' and
'unsafeFindMut'.

This module provides both unsafe (fast) and safe (bounds-checked) APIs.
The unsafe variants follow the same convention as vector libraries:
they are fast but can crash on invalid input. The safe variants
return Maybe values or Bool success indicators.

Elements are represented by 'Key' values which wrap Word indices.
-}
module Data.UnionFind.Linear (
  -- * Types
  UnionFind,
  Key (..),

  -- * Construction
  empty,
  emptyL,

  -- * Dynamic extension
  fresh,

  -- * Core operations (safe - bounds checked)
  find,
  findMut,
  union,
  equivalent,

  -- * Core operations (unsafe - fast)
  unsafeFind,
  unsafeFindMut,
  unsafeUnion,
  unsafeUnionTo,
  unsafeEquivalent,

  -- * Queries
  size,

  -- * Debug
  unsafeToLists,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear.Unboxed qualified as Array
import Data.Array.Mutable.Linear.Unboxed.Internal (UArray (..))
import Data.Coerce qualified
import Data.Functor.Linear qualified as Data
import Data.Linear.Witness.Compat (fromPB)
import Data.UnionFind.Linear.Internal
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as MU
import GHC.Base (runRW#, unIO)
import Prelude.Linear hiding (Eq (..), Num (..), Ord (..), find, (+), (-))
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Num (..), Ord (..))
import Prelude qualified as P

-- Helper function to convert Key to Int for array indexing
keyToInt :: Key -> Int
{-# INLINE keyToInt #-}
keyToInt = Data.Coerce.coerce $ fromIntegral @Word @Int

-- | Create an empty union-find structure.
empty :: (Movable b) => (UnionFind %1 -> b) %1 -> b
empty f = Array.unsafeAlloc 0 \parent ->
  Array.unsafeAllocBeside 0 parent & \(rank, parent) ->
    f (UnionFind 0 0 parent rank)

emptyL :: Linearly %1 -> UnionFind
emptyL lin = flip runReader lin Control.do
  parents <- asks $ Array.unsafeAllocL 0 . fromPB
  ranks <- asks $ Array.unsafeAllocL 0 . fromPB
  Control.pure $ UnionFind 0 0 parents ranks

{- | Non-allocating parent-chain walk on the raw backing buffer: one unsafe
block per find instead of one boxed @(Ur, array)@ pair per hop (which is
what 'Array.unsafeGet' costs). Read-only — the array is returned unchanged
and no path compression is performed.
-}
unsafeFindRoot :: Key -> UArray Key %1 -> (Ur Key, UArray Key)
{-# NOINLINE unsafeFindRoot #-}
unsafeFindRoot !k0 = Unsafe.toLinear \arr0 ->
  case arr0 of
    UArray mu ->
      let go !k =
            MU.unsafeRead mu (keyToInt k) P.>>= \p ->
              if p == k then P.pure k else go p
       in case runRW# (unIO (go k0)) of
            (# _, root #) -> (Ur root, arr0)

{- | Find the representative (root) of the set containing the given element,
with path compression for efficiency.

__Unsafe__: Does not check bounds. Will crash if key >= size.
-}
{-# INLINE unsafeFindMut #-}
unsafeFindMut :: Key -> UnionFind %1 -> (Ur Key, UnionFind)
unsafeFindMut x (UnionFind n cap parent rank) =
  findRoot x parent rank
  where
    findRoot :: Key -> UArray Key %1 -> UArray Word %1 -> (Ur Key, UnionFind)
    findRoot i p r =
      Array.unsafeGet (keyToInt i) p & \(Ur parentKey, p) ->
        if i == parentKey
          then (Ur i, UnionFind n cap p r)
          else
            findRoot parentKey p r & \(Ur root, UnionFind _ _ p r) ->
              -- Path compression: make i point directly to root
              Array.unsafeSet (keyToInt i) root p & \p ->
                (Ur root, UnionFind n cap p r)

{- | Find the representative (root) of the set containing the given element,
with path compression for efficiency.
Returns Nothing if the key is out of bounds.
-}
{-# INLINE findMut #-}
findMut :: Key -> UnionFind %1 -> (Ur (Maybe Key), UnionFind)
findMut (Key x) (UnionFind n cap parent rank)
  | x >= n = (Ur Nothing, UnionFind n cap parent rank)
  | otherwise =
      unsafeFindMut (Key x) (UnionFind n cap parent rank) & \(!root, !uf') ->
        (Just Data.<$> root, uf')

{- |
Find the representative (root) of the set containing the given element.
No path compression (read-only; see the module header).

__Unsafe__: Does not check bounds. Will crash if key >= size.
-}
{-# INLINE unsafeFind #-}
unsafeFind :: Key -> UnionFind %1 -> (Ur Key, UnionFind)
unsafeFind x (UnionFind n cap parent rank) =
  unsafeFindRoot x parent & \(root, parent) ->
    (root, UnionFind n cap parent rank)

{- | Find the representative (root) of the set containing the given element.
No path compression (read-only; see the module header).
Returns Nothing if the key is out of bounds.
-}
{-# INLINE find #-}
find :: Key -> UnionFind %1 -> (Ur (Maybe Key), UnionFind)
find (Key x) (UnionFind n cap parent rank)
  | x >= n = (Ur Nothing, UnionFind n cap parent rank)
  | otherwise =
      unsafeFind (Key x) (UnionFind n cap parent rank) & \(!root, !uf') ->
        (Just Data.<$> root, uf')

{- | Unite the sets containing the two given elements using union-by-rank.
If the elements are already in the same set, this is a no-op.
Returns the representative (root) of the unified set.

__Unsafe__: Does not check bounds. Will crash if keys >= size.
-}
{-# INLINE unsafeUnion #-}
unsafeUnion :: Key -> Key -> UnionFind %1 -> (Ur Key, UnionFind)
unsafeUnion x y uf =
  unsafeFind x uf & \(Ur rootX, uf) ->
    unsafeFind y uf & \(Ur rootY, uf) ->
      if rootX == rootY
        then (Ur rootX, uf) -- Already in same set, return the root
        else unionRoots rootX rootY uf
  where
    unionRoots :: Key -> Key -> UnionFind %1 -> (Ur Key, UnionFind)
    unionRoots rx ry (UnionFind n cap parent rank) =
      Array.unsafeGet (keyToInt rx) rank & \(Ur rankX, rank) ->
        Array.unsafeGet (keyToInt ry) rank & \(Ur rankY, rank) -> DataFlow.do
          let (pid, cid)
                | rankX < rankY = (ry, rx)
                | otherwise = (rx, ry)
          parent <- Array.unsafeSet (keyToInt cid) pid parent
          rank <-
            if rankX == rankY
              then
                Array.unsafeGet (keyToInt pid) rank & \(Ur w, rank) ->
                  Array.unsafeSet (keyToInt pid) (w + 1) rank
              else rank
          (Ur pid, UnionFind n cap parent rank)

{- | Unite two root sets, making the first root the representative.

__Unsafe__: Both keys must be distinct roots in bounds.
-}
{-# INLINE unsafeUnionTo #-}
unsafeUnionTo :: Key -> Key -> UnionFind %1 -> (Ur Key, UnionFind)
unsafeUnionTo leader sub (UnionFind n cap parent rank) =
  Array.unsafeGet (keyToInt leader) rank & \(Ur leaderRank, rank) ->
    Array.unsafeGet (keyToInt sub) rank & \(Ur subRank, rank) -> DataFlow.do
      parent <- Array.unsafeSet (keyToInt sub) leader parent
      rank <- Array.unsafeSet (keyToInt leader) (P.max leaderRank (subRank + 1)) rank
      (Ur leader, UnionFind n cap parent rank)

{- | Unite the sets containing the two given elements using union-by-rank.
Returns Nothing if either key is out of bounds, otherwise returns Just the representative key of the unified set.
-}
{-# INLINE union #-}
union :: Key -> Key -> UnionFind %1 -> (Ur (Maybe Key), UnionFind)
union (Key x) (Key y) (UnionFind n cap parent rank)
  | x >= n || y >= n = (Ur Nothing, UnionFind n cap parent rank)
  | otherwise = unsafeUnion (Key x) (Key y) (UnionFind n cap parent rank) & \(Ur root, uf') -> (Ur (Just root), uf')

{- | Check if two elements are in the same set.

__Unsafe__: Does not check bounds. Will crash if keys >= size.
-}
unsafeEquivalent :: Key -> Key -> UnionFind %1 -> (Ur Bool, UnionFind)
unsafeEquivalent x y uf =
  unsafeFind x uf & \(Ur rootX, uf) ->
    unsafeFind y uf & \(Ur rootY, uf) ->
      (Ur (rootX == rootY), uf)

{- | Check if two elements are in the same set.
Returns Nothing if either key is out of bounds.
-}
equivalent :: Key -> Key -> UnionFind %1 -> (Ur (Maybe Bool), UnionFind)
equivalent (Key x) (Key y) (UnionFind n cap parent rank)
  | x >= n || y >= n = (Ur Nothing, UnionFind n cap parent rank)
  | otherwise = unsafeEquivalent (Key x) (Key y) (UnionFind n cap parent rank) & \(Ur result, uf') -> (Ur (Just result), uf')

{- | Extend the union-find structure with a new element and return its key.
The new element starts in its own singleton set.

Amortized O(1): while the backing arrays have spare capacity this is two
in-place writes; on exhaustion both arrays double (via 'Array.unsafeResize').
-}
{-# INLINE fresh #-}
fresh :: UnionFind %1 -> (Ur Key, UnionFind)
fresh (UnionFind n cap parent rank) =
  let !i = keyToInt (Key n)
   in if i P.< cap
        then
          Array.unsafeSet i (Key n) parent & \parent ->
            Array.unsafeSet i 0 rank & \rank ->
              (Ur (Key n), UnionFind (n + 1) cap parent rank)
        else
          let !cap' = P.max 16 (cap P.* 2)
           in Array.unsafeResize cap' parent & \parent ->
                Array.unsafeResize cap' rank & \rank ->
                  Array.unsafeSet i (Key n) parent & \parent ->
                    Array.unsafeSet i 0 rank & \rank ->
                      (Ur (Key n), UnionFind (n + 1) cap' parent rank)

-- | Get the number of elements in the union-find structure.
size :: UnionFind %1 -> (Ur Word, UnionFind)
size (UnionFind n cap parent rank) = (Ur n, UnionFind n cap parent rank)

-- | Snapshot size, live parent entries, and live ranks. Debug\/'Display' only.
unsafeToLists :: UnionFind %1 -> (Ur (Word, [Key], [Word]), UnionFind)
{-# NOINLINE unsafeToLists #-}
unsafeToLists = Unsafe.toLinear \uf ->
  case uf of
    UnionFind n _ (UArray pmu) (UArray rmu) ->
      case runRW#
        ( unIO
            ( U.freeze (MU.take (keyToInt (Key n)) pmu) P.>>= \ps ->
                U.freeze (MU.take (keyToInt (Key n)) rmu) P.>>= \rs ->
                  P.pure (U.toList ps, U.toList rs)
            )
        ) of
        (# _, (ps, rs) #) -> (Ur (n, ps, rs), uf)
