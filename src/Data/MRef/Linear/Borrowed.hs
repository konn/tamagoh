{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.MRef.Linear.Borrowed (MRef, newMRef, tryTakeMRef) where

import Control.Concurrent.MVar (MVar, newEmptyMVar, tryTakeMVar)
import Control.Functor.Linear qualified as Control
import Control.Monad qualified as P
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe

newtype MRef a = MRef (MVar a)

newMRef :: BO α (Mut α (MRef a), Lend α (MRef a))
{-# NOINLINE newMRef #-}
newMRef = Control.do
  Ur !mvar <- unsafeSystemIOToBO (Ur P.<$!> newEmptyMVar)
  Control.pure (UnsafeAlias (MRef mvar), UnsafeAlias (MRef mvar))

tryTakeMRef :: Mut α (MRef a) %1 -> BO α (Maybe a, Mut α (MRef a))
{-# NOINLINE tryTakeMRef #-}
tryTakeMRef = Unsafe.toLinear \(UnsafeAlias (MRef mvar)) -> Control.do
  Ur !res <- unsafeSystemIOToBO (Ur P.<$!> tryTakeMVar mvar)
  Control.pure (res, UnsafeAlias (MRef mvar))
