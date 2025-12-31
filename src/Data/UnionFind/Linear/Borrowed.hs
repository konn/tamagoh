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
  find,
  fresh,
  union,
  equivalent,

  -- * unsafe operations
  unsafeThaw,
  unsafeFind,
  unsafeUnion,
  unsafeEquivalent,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Data.Bifunctor.Linear qualified as Bi
import Data.Ref.Linear qualified as Ref
import Data.UnionFind.Linear (Key)
import Data.UnionFind.Linear qualified as Raw
import Data.UnionFind.Linear.Borrowed.Internal
import Data.UnionFind.Linear.Immutable (freeze, thaw, unsafeThaw)
import Prelude.Linear hiding (find)

empty :: Linearly %1 -> UnionFind
empty = runReader Control.do
  uf <- asks Raw.emptyL
  asks $ UF . Ref.new uf

{- | Find the representative key of the set containing the given key.

NOTE: This function uses path compression, which mutates the internal state;
but this SHOULD NOT affect the external behavior of the union-find structure,
so we provide it in for _any_ 'Borrow's (in particular, for 'Share's)  unrestrictedly.
-}
find ::
  forall k α.
  Key -> Borrow k α UnionFind %1 -> BO α (Ur (Maybe Key))
find key (UnsafeAlias bor) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias bor :: Mut α _)
  (!key, UnsafeAlias !a) <- updateRef (Control.pure . Raw.find key) borRef
  Control.pure $ unsafeLeak a `lseq` key

unsafeFind :: forall k α. Key -> Borrow k α UnionFind %1 -> BO α (Ur Key)
unsafeFind key (UnsafeAlias bor) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias bor :: Mut α _)
  (!key, UnsafeAlias !a) <- updateRef (Control.pure . Raw.unsafeFind key) borRef
  Control.pure $ unsafeLeak a `lseq` key

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
unsafeEquivalent k1 k2 (UnsafeAlias uf) = Control.do
  let %1 borRef = coerceUF (UnsafeAlias uf :: Mut α _)
  (r, uf) <- updateRef (Control.pure . Raw.unsafeEquivalent k1 k2) borRef
  Control.pure $ uf `lseq` r
