{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- | Efficient union-find data structure with path compression,
using linear types for safe mutation and unboxed vectors for performance.

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
  new,
  newL,

  -- * Dynamic extension
  fresh,

  -- * Core operations (safe - bounds checked)
  find,
  union,
  equivalent,

  -- * Core operations (unsafe - fast)
  unsafeFind,
  unsafeUnion,
  unsafeEquivalent,

  -- * Queries
  size,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Data.Coerce qualified
import Data.Hashable (Hashable)
import Data.Linear.Witness.Compat (fromPB)
import Data.Ord.Linear qualified as Linear
import Data.Vector.Mutable.Linear.Unboxed (Vector)
import Data.Vector.Mutable.Linear.Unboxed qualified as Vector
import Prelude.Linear hiding (Eq (..), Num (..), Ord (..), find, (+), (-))
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Num (..), Ord (..))

{- | A key representing an element in the union-find structure.
Keys are zero-indexed Word values.
-}
newtype Key = Key {getKey :: Word}
  deriving newtype
    ( Prelude.Eq
    , Prelude.Ord
    , Prelude.Num
    , Show
    , Enum
    , Bounded
    , Hashable
    , Consumable
    , Dupable
    , Movable
    )

instance Linear.Eq Key where
  (==) = Unsafe.coerce $ (Prelude.==) @Word
  {-# INLINE (==) #-}

instance Linear.Ord Key where
  compare = Unsafe.coerce $ Prelude.compare @Word
  {-# INLINE compare #-}
  (<=) = Unsafe.coerce $ (Prelude.<=) @Word
  {-# INLINE (<=) #-}
  (<) = Unsafe.coerce $ (Prelude.<) @Word
  {-# INLINE (<) #-}
  (>=) = Unsafe.coerce $ (Prelude.>=) @Word
  {-# INLINE (>=) #-}
  (>) = Unsafe.coerce $ (Prelude.>) @Word
  {-# INLINE (>) #-}

{- | A union-find (disjoint-set) data structure specialized for 'Key' elements.
Elements are represented by indices 0..n-1.

The structure maintains two unboxed vectors:
* Parent pointers for the tree structure
* Ranks for the union-by-rank heuristic

All fields are strict to prevent space leaks.
-}
data UnionFind where
  UnionFind :: !Word -> !(Vector Word) %1 -> !(Vector Word) %1 -> UnionFind

instance LinearOnly UnionFind where
  linearOnly = UnsafeLinearOnly

-- Helper function to convert Key to Int for array indexing
keyToInt :: Key -> Int
{-# INLINE keyToInt #-}
keyToInt = Data.Coerce.coerce $ fromIntegral @Word @Int

-- | Create an empty union-find structure.
empty :: (UnionFind %1 -> Ur b) %1 -> Ur b
empty f = Vector.empty \parent -> Vector.empty \rank ->
  f (UnionFind 0 parent rank)

emptyL :: Linearly %1 -> UnionFind
emptyL lin = flip runReader lin Control.do
  parents <- asks $ Vector.emptyL . fromPB
  ranks <- asks $ Vector.emptyL . fromPB
  Control.pure $ UnionFind 0 parents ranks

{- | Create a union-find structure with @n@ elements (0..n-1).
Initially, each element is in its own singleton set.
-}
new :: Word -> (UnionFind %1 -> Ur b) %1 -> Ur b
new n f =
  Vector.fromList [0 .. n - 1] \parent ->
    Vector.fromList (replicate (fromIntegral n) 0) \rank ->
      f (UnionFind n parent rank)

newL :: Word -> Linearly %1 -> UnionFind
newL n lin = flip runReader lin Control.do
  parents <- asks $ Vector.fromListL [0 .. n - 1] . fromPB
  ranks <- asks $ Vector.fromListL (replicate (fromIntegral n) 0) . fromPB
  Control.pure $ UnionFind n parents ranks

{- | Find the representative (root) of the set containing the given element,
with path compression for efficiency.

__Unsafe__: Does not check bounds. Will crash if key >= size.
-}
unsafeFind :: Key -> UnionFind %1 -> (Ur Key, UnionFind)
unsafeFind x (UnionFind n parent rank) =
  findRoot x parent rank
  where
    findRoot :: Key -> Vector Word %1 -> Vector Word %1 -> (Ur Key, UnionFind)
    findRoot i p r =
      Vector.get (keyToInt i) p & \(Ur parentI, p') ->
        let parentKey = Key parentI
         in if i == parentKey
              then (Ur i, UnionFind n p' r)
              else
                findRoot parentKey p' r & \(Ur root, UnionFind _ p'' r') ->
                  -- Path compression: make i point directly to root
                  Vector.set (keyToInt i) (let Key w = root in w) p'' & \p''' ->
                    (Ur root, UnionFind n p''' r')

{- | Find the representative (root) of the set containing the given element,
with path compression for efficiency.
Returns Nothing if the key is out of bounds.
-}
find :: Key -> UnionFind %1 -> (Ur (Maybe Key), UnionFind)
find (Key x) (UnionFind n parent rank)
  | x >= n = (Ur Nothing, UnionFind n parent rank)
  | otherwise = unsafeFind (Key x) (UnionFind n parent rank) & \(Ur root, uf') -> (Ur (Just root), uf')

{- | Unite the sets containing the two given elements using union-by-rank.
If the elements are already in the same set, this is a no-op.

__Unsafe__: Does not check bounds. Will crash if keys >= size.
-}
unsafeUnion :: Key -> Key -> UnionFind %1 -> UnionFind
unsafeUnion x y uf =
  unsafeFind x uf & \(Ur rootX, uf') ->
    unsafeFind y uf' & \(Ur rootY, uf'') ->
      if rootX == rootY
        then uf'' -- Already in same set
        else unionRoots rootX rootY uf''
  where
    unionRoots :: Key -> Key -> UnionFind %1 -> UnionFind
    unionRoots rx ry (UnionFind n parent rank) =
      Vector.get (keyToInt rx) rank & \(Ur rankX, rank') ->
        Vector.get (keyToInt ry) rank' & \(Ur rankY, rank'') ->
          if rankX < rankY
            then
              -- Make ry the parent of rx
              Vector.set (keyToInt rx) (let Key w = ry in w) parent & \parent' ->
                UnionFind n parent' rank''
            else
              if rankX > rankY
                then
                  -- Make rx the parent of ry
                  Vector.set (keyToInt ry) (let Key w = rx in w) parent & \parent' ->
                    UnionFind n parent' rank''
                else
                  -- Equal ranks: make ry parent of rx and increment ry's rank
                  Vector.set (keyToInt rx) (let Key w = ry in w) parent & \parent' ->
                    Vector.set (keyToInt ry) (rankY + 1) rank'' & \rank''' ->
                      UnionFind n parent' rank'''

{- | Unite the sets containing the two given elements using union-by-rank.
Returns False if either key is out of bounds, True otherwise.
-}
union :: Key -> Key -> UnionFind %1 -> (Ur Bool, UnionFind)
union (Key x) (Key y) (UnionFind n parent rank)
  | x >= n || y >= n = (Ur False, UnionFind n parent rank)
  | otherwise = unsafeUnion (Key x) (Key y) (UnionFind n parent rank) & \uf' -> (Ur True, uf')

{- | Check if two elements are in the same set.

__Unsafe__: Does not check bounds. Will crash if keys >= size.
-}
unsafeEquivalent :: Key -> Key -> UnionFind %1 -> (Ur Bool, UnionFind)
unsafeEquivalent x y uf =
  unsafeFind x uf & \(Ur rootX, uf') ->
    unsafeFind y uf' & \(Ur rootY, uf'') ->
      (Ur (rootX == rootY), uf'')

{- | Check if two elements are in the same set.
Returns Nothing if either key is out of bounds.
-}
equivalent :: Key -> Key -> UnionFind %1 -> (Ur (Maybe Bool), UnionFind)
equivalent (Key x) (Key y) (UnionFind n parent rank)
  | x >= n || y >= n = (Ur Nothing, UnionFind n parent rank)
  | otherwise = unsafeEquivalent (Key x) (Key y) (UnionFind n parent rank) & \(Ur result, uf') -> (Ur (Just result), uf')

{- | Extend the union-find structure with a new element and return its key.
The new element starts in its own singleton set.
-}
fresh :: UnionFind %1 -> (Ur Key, UnionFind)
fresh (UnionFind n parent rank) =
  let newIdx = n
      newKey' = Key newIdx
   in Vector.push newIdx parent & \parent' ->
        Vector.push 0 rank & \rank' ->
          (Ur newKey', UnionFind (n + 1) parent' rank')

-- | Get the number of elements in the union-find structure.
size :: UnionFind %1 -> (Ur Word, UnionFind)
size (UnionFind n parent rank) = (Ur n, UnionFind n parent rank)
