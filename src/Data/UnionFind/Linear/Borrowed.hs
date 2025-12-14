{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A pure-borrow based union-find data structure implementation.
module Data.UnionFind.Linear.Borrowed (
  Key,
  UnionFind,
  -- Constructors,
  new,
  empty,
  -- operations
  find,
  fresh,
  union,
  equivalent,
  -- unsafe ops
  unsafeFind,
  unsafeUnion,
  unsafeEquivalent,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.UnionFind.Linear (Key, UnionFind)
import Data.UnionFind.Linear qualified as Raw
import Prelude.Linear hiding (find)
import Unsafe.Linear qualified as Unsafe

new :: Word -> Linearly %1 -> (Mut α UnionFind, Lend α UnionFind)
new capacity = borrowLinearOnly . Raw.newL capacity

empty :: Linearly %1 -> (Mut α UnionFind, Lend α UnionFind)
empty = borrowLinearOnly . Raw.emptyL

{- | Find the representative key of the set containing the given key.

NOTE: This function uses path compression, which mutates the internal state;
but this SHOULD NOT affect the external behavior of the union-find structure,
so we provide it in for _any_ 'Borrow's (in particular, for 'Share's)  unrestrictedly.
-}
find :: Key -> Borrow k α UnionFind %1 -> BO α (Maybe (Ur Key))
{-# NOINLINE find #-}
find key = Unsafe.toLinear \(UnsafeAlias uf) -> case Raw.find key uf of
  -- We need to force a thunk here to force the mutations.
  (mkey, !_) -> Control.pure mkey

unsafeFind :: Key -> Borrow k α UnionFind %1 -> BO α (Ur Key)
{-# NOINLINE unsafeFind #-}
unsafeFind key = Unsafe.toLinear \(UnsafeAlias uf) -> case Raw.unsafeFind key uf of
  (k, !_) -> Control.pure k

fresh :: Mut α UnionFind %1 -> BO α (Ur Key, UnionFind)
fresh (UnsafeAlias uf) = case Raw.fresh uf of
  (k, !uf') -> Control.pure (k, uf')

union ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur (Maybe Key), UnionFind)
union k1 k2 (UnsafeAlias uf) = case Raw.union k1 k2 uf of
  (mk, !uf') -> Control.pure (mk, uf')

unsafeUnion ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur Key, UnionFind)
unsafeUnion k1 k2 (UnsafeAlias uf) = case Raw.unsafeUnion k1 k2 uf of
  (k, !uf') -> Control.pure (k, uf')

equivalent :: Key -> Key -> Borrow k α UnionFind %1 -> BO α (Ur (Maybe Bool))
equivalent k1 k2 = Unsafe.toLinear \(UnsafeAlias uf) -> case Raw.equivalent k1 k2 uf of
  (b, !_) -> Control.pure b

{- |
NOTE: This function uses path compression, which mutates the internal state;
but this SHOULD NOT affect the external behavior of the union-find structure,
so we provide it in for _any_ 'Borrow's (in particular, for 'Share's)  unrestrictedly.
-}
unsafeEquivalent :: Key -> Key -> Borrow k α UnionFind %1 -> BO α (Ur Bool)
unsafeEquivalent k1 k2 = Unsafe.toLinear \(UnsafeAlias uf) -> case Raw.unsafeEquivalent k1 k2 uf of
  (b, !_) -> Control.pure b
