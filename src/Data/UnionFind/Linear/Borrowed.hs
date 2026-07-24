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
  freeze,
  thaw,

  -- * Constructors,
  empty,

  -- * operations
  member,
  find,
  fresh,
  union,
  equivalent,

  -- * unsafe operations
  unsafeThaw,
  unsafeFind,
  unsafeUnion,
  unsafeUnionTo,
  unsafeEquivalent,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Data.Bifunctor.Linear qualified as Bi
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as Ref
import Data.UnionFind.Linear (Key)
import Data.UnionFind.Linear qualified as Raw
import Data.UnionFind.Linear.Borrowed.Internal
import Data.UnionFind.Linear.Immutable (freeze, thaw, unsafeThaw)
import Data.UnionFind.Linear.Internal qualified as Raw
import Prelude.Linear hiding (find)
import Prelude qualified as P

empty :: Linearly %1 -> UnionFind
empty = runReader Control.do
  uf <- asks Raw.emptyL
  asks $ UF . Ref.new uf

{- | Find the representative key of the set containing the given key.

Read-only: the raw lookup performs no path compression (the compressing
variants are 'Raw.findMut'\/'Raw.unsafeFindMut', rejected for borrowed
lookups in TUNE-PLAN P9.14), so this reads through a shared alias without
writing the union-find back (P9.20 discipline).
-}
{-# INLINE find #-}
find ::
  forall k α m.
  Key -> Borrow k α UnionFind %m -> BO α (Ur (Maybe Key))
find key bor =
  share bor & \(Ur bor) -> Control.do
    let %1 borRef = coerceUF bor
    Ur (UnsafeAlias !uf) <- Ref.readShare borRef
    case Raw.find key uf of
      (!key, !uf) -> Control.pure $ unsafeLeak uf `lseq` key

{-# INLINE member #-}
member ::
  forall k α m.
  Key -> Borrow k α UnionFind %m -> BO α (Ur Bool)
member key bor =
  share bor & \(Ur bor) -> Control.do
    let %1 borRef = coerceUF bor
    Ur (UnsafeAlias (Raw.UnionFind n _ _ _)) <- Ref.readShare borRef
    Control.pure $ Ur (Raw.getKey key P.< n)

{-# INLINE unsafeFind #-}
unsafeFind :: forall k α m. Key -> Borrow k α UnionFind %m -> BO α (Ur Key)
unsafeFind key bor =
  share bor & \(Ur bor) -> Control.do
    let %1 borRef = coerceUF bor
    Ur (UnsafeAlias !uf) <- Ref.readShare borRef
    case Raw.unsafeFind key uf of
      (!key, !uf) -> Control.pure $ unsafeLeak uf `lseq` key

{-# INLINE fresh #-}
fresh :: Mut α UnionFind %1 -> BO α (Ur Key, Mut α UnionFind)
fresh uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> Ref.update (Control.pure . Raw.fresh) borRef

{-# INLINE union #-}
union ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur (Maybe Key), Mut α UnionFind)
union k1 k2 uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> Ref.update (Control.pure . Raw.union k1 k2) borRef

{-# INLINE unsafeUnion #-}
unsafeUnion ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur Key, Mut α UnionFind)
unsafeUnion k1 k2 uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> Ref.update (Control.pure . Raw.unsafeUnion k1 k2) borRef

{-# INLINE unsafeUnionTo #-}
unsafeUnionTo ::
  Key ->
  Key ->
  Mut α UnionFind %1 ->
  BO α (Ur Key, Mut α UnionFind)
unsafeUnionTo leader sub uf = Control.do
  let %1 borRef = coerceUF uf
  Bi.second recoerceUF Control.<$> Ref.update (Control.pure . Raw.unsafeUnionTo leader sub) borRef

-- | Read-only equivalence check (no path compression; P9.20 discipline).
{-# INLINE equivalent #-}
equivalent ::
  forall k α m.
  Key -> Key -> Borrow k α UnionFind %m -> BO α (Ur (Maybe Bool))
equivalent k1 k2 bor =
  share bor & \(Ur bor) -> Control.do
    let %1 borRef = coerceUF bor
    Ur (UnsafeAlias !uf) <- Ref.readShare borRef
    case Raw.equivalent k1 k2 uf of
      (!r, !uf) -> Control.pure $ unsafeLeak uf `lseq` r

-- | Read-only equivalence check (no path compression; P9.20 discipline).
{-# INLINE unsafeEquivalent #-}
unsafeEquivalent ::
  forall k α m.
  Key -> Key -> Borrow k α UnionFind %m -> BO α (Ur Bool)
unsafeEquivalent k1 k2 bor =
  share bor & \(Ur bor) -> Control.do
    let %1 borRef = coerceUF bor
    Ur (UnsafeAlias !uf) <- Ref.readShare borRef
    case Raw.unsafeEquivalent k1 k2 uf of
      (!r, !uf) -> Control.pure $ unsafeLeak uf `lseq` r
