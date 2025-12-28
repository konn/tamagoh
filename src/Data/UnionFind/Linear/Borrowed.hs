{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | A pure-borrow based union-find data structure implementation.
module Data.UnionFind.Linear.Borrowed (
  Key,
  UnionFind,
  -- Constructors,
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

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.UnionFind.Linear (Key)
import Data.UnionFind.Linear qualified as Raw
import Prelude.Linear hiding (find)
import Unsafe.Linear qualified as Unsafe

-- | UnionFind which can be borrowed mutably, using indirection.
newtype UnionFind = UF (Ref Raw.UnionFind)
  deriving newtype (LinearOnly)

instance Consumable UnionFind where
  consume (UF ref) = consume $ freeRef ref
  {-# INLINE consume #-}

empty :: Linearly %1 -> UnionFind
empty = runReader Control.do
  uf <- asks Raw.emptyL
  asks $ UF . Ref.new uf

coerceUF :: Borrow k α UnionFind %1 -> Borrow k α (Ref Raw.UnionFind)
{-# INLINE coerceUF #-}
coerceUF = coerceLin

recoerceUF :: Borrow k α (Ref Raw.UnionFind) %1 -> Borrow k α UnionFind
{-# INLINE recoerceUF #-}
recoerceUF = coerceLin

coerceLin :: (Coercible a b) => a %1 -> b
{-# INLINE coerceLin #-}
coerceLin = Unsafe.toLinear coerce

{- | Find the representative key of the set containing the given key.

NOTE: This function uses path compression, which mutates the internal state;
but this SHOULD NOT affect the external behavior of the union-find structure,
so we provide it in for _any_ 'Borrow's (in particular, for 'Share's)  unrestrictedly.
-}
find ::
  forall k α.
  Key -> Borrow k α UnionFind %1 -> BO α (Ur (Maybe Key))
{-# NOINLINE find #-}
find key (UnsafeAlias bor) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias bor :: Mut α _)
  (key, UnsafeAlias !a) <- updateRef (Control.pure . Raw.find key) borRef
  Control.pure $ freeRef a `lseq` key

unsafeFind :: forall k α. Key -> Borrow k α UnionFind %1 -> BO α (Ur Key)
{-# NOINLINE unsafeFind #-}
unsafeFind key (UnsafeAlias bor) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias bor :: Mut α _)
  (key, UnsafeAlias !a) <- updateRef (Control.pure . Raw.unsafeFind key) borRef
  Control.pure $ freeRef a `lseq` key

fresh :: Mut α UnionFind %1 -> BO α (Ur Key, Mut α UnionFind)
fresh uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> updateRef (Control.pure . Raw.fresh) borRef

union ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur (Maybe Key), Mut α UnionFind)
union k1 k2 uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> updateRef (Control.pure . Raw.union k1 k2) borRef

unsafeUnion ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur Key, Mut α UnionFind)
unsafeUnion k1 k2 uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> updateRef (Control.pure . Raw.unsafeUnion k1 k2) borRef

equivalent ::
  forall k α.
  Key -> Key -> Borrow k α UnionFind %1 -> BO α (Ur (Maybe Bool))
{-# NOINLINE equivalent #-}
equivalent k1 k2 (UnsafeAlias uf) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias uf :: Mut α _)
  (r, uf) <- updateRef (Control.pure . Raw.equivalent k1 k2) borRef
  Control.pure $ uf `lseq` r

{- |
NOTE: This function uses path compression, which mutates the internal state;
but this SHOULD NOT affect the external behavior of the union-find structure,
so we provide it in for _any_ 'Borrow's (in particular, for 'Share's)  unrestrictedly.
-}
unsafeEquivalent ::
  forall k α.
  Key -> Key -> Borrow k α UnionFind %1 -> BO α (Ur Bool)
{-# NOINLINE unsafeEquivalent #-}
unsafeEquivalent k1 k2 (UnsafeAlias uf) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias uf :: Mut α _)
  (r, uf) <- updateRef (Control.pure . Raw.unsafeEquivalent k1 k2) borRef
  Control.pure $ uf `lseq` r
