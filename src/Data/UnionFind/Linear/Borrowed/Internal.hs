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
import Control.Monad.Borrow.Pure.BO.Unsafe
import Control.Monad.Borrow.Pure.Utils (coerceLin, unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Ref.Linear (Ref)
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as Ref
import Data.UnionFind.Linear qualified as Raw
import Prelude.Linear hiding (find)
import Text.Show.Borrowed
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- | UnionFind which can be borrowed mutably, using indirection.
newtype UnionFind = UF (Ref Raw.UnionFind)
  deriving newtype (LinearOnly)

instance Dupable UnionFind where
  dup2 = Unsafe.toLinear \(UF ref) -> DataFlow.do
    !uf <- Unsafe.toLinear Ref.free ref
    (ref, !uf2) <- Unsafe.toLinear (\(_, uf2) -> (ref, uf2)) $ dup2 uf
    (lin, ref) <- withLinearly ref
    (UF ref, UF $! Ref.new uf2 lin)

instance Display UnionFind where
  displayPrec _ ref = Control.do
    let %1 borRef = coerceUF ref
    Ur (UnsafeAlias !uf) <- Ref.readShare borRef
    case Raw.unsafeToLists uf of
      (Ur (n, ps, rs), uf) ->
        Control.pure $
          unsafeLeak uf `lseq`
            Ur
              ( showString "UnionFind "
                  P.. showString "{ size = "
                  P.. shows n
                  P.. showString ", parents = "
                  P.. shows ps
                  P.. showString ", ranks = "
                  P.. shows rs
                  P.. showString " }"
              )

instance Consumable UnionFind where
  consume (UF ref) = consume $ Ref.free ref
  {-# INLINE consume #-}

coerceUF :: Borrow k α UnionFind %1 -> Borrow k α (Ref Raw.UnionFind)
{-# INLINE coerceUF #-}
coerceUF = coerceLin

recoerceUF :: Borrow k α (Ref Raw.UnionFind) %1 -> Borrow k α UnionFind
{-# INLINE recoerceUF #-}
recoerceUF = coerceLin
