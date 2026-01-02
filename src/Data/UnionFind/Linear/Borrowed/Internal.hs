{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | A pure-borrow based union-find data structure implementation.
module Data.UnionFind.Linear.Borrowed.Internal (
  module Data.UnionFind.Linear.Borrowed.Internal,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (coerceLin)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.UnionFind.Linear qualified as Raw
import Data.UnionFind.Linear.Internal qualified as Raw
import Data.Vector.Mutable.Linear.Unboxed qualified as Vector
import Prelude.Linear hiding (find)
import Text.Show.Borrowed
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- | UnionFind which can be borrowed mutably, using indirection.
newtype UnionFind = UF (Ref Raw.UnionFind)
  deriving newtype (LinearOnly)

instance Dupable UnionFind where
  dup2 = Unsafe.toLinear \(UF ref) -> DataFlow.do
    !uf <- Unsafe.toLinear freeRef ref
    (ref, !uf2) <- Unsafe.toLinear (\(_, uf2) -> (ref, uf2)) $ dup2 uf
    (lin, ref) <- withLinearly ref
    (UF ref, UF $! Ref.new uf2 lin)

instance Display UnionFind where
  displayPrec _ ref = Control.do
    let %1 borRef = coerceUF ref
    Ur (UnsafeAlias (Raw.UnionFind !n !parent !rank)) <- readSharedRef borRef
    let Ur ps = Vector.toList parent
        Ur rs = Vector.toList rank
    Control.pure $
      Ur $
        showString "UnionFind "
          P.. showString "{ size = "
          P.. shows n
          P.. showString ", parents = "
          P.. shows ps
          P.. showString ", ranks = "
          P.. shows rs
          P.. showString " }"

instance Consumable UnionFind where
  consume (UF ref) = consume $ freeRef ref
  {-# INLINE consume #-}

coerceUF :: Borrow k α UnionFind %1 -> Borrow k α (Ref Raw.UnionFind)
{-# INLINE coerceUF #-}
coerceUF = coerceLin

recoerceUF :: Borrow k α (Ref Raw.UnionFind) %1 -> Borrow k α UnionFind
{-# INLINE recoerceUF #-}
recoerceUF = coerceLin
