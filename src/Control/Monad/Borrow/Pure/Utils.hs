{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Control.Monad.Borrow.Pure.Utils (
  unsafeLeak,
  deepCloneArray,
  deepCloneArray',
  forReborrowing_,
  forReborrowing,
  Borrows (..),
  swapTuple,
  nubHash,
  coerceLin,
) where

import Control.Monad.Borrow.Pure.Experimental.Borrows
import Control.Monad.Borrow.Pure.Experimental.Loop
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear (Array)
import Data.Array.Mutable.Linear qualified as Array
import Data.Coerce (Coercible, coerce)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

unsafeLeak :: a %1 -> ()
{-# INLINE unsafeLeak #-}
unsafeLeak = Unsafe.toLinear \ !_ -> ()

deepCloneArray :: forall a. (Dupable a) => Array a %1 -> (Array a, Array a)
{-# INLINE deepCloneArray #-}
deepCloneArray = deepCloneArray' dup

deepCloneArray' :: forall a. (a %1 -> (a, a)) -> Array a %1 -> (Array a, Array a)
deepCloneArray' clone arr =
  Array.size arr & \(Ur size, arr) ->
    if size == 0
      then Array.allocBeside 0 undefined arr
      else
        Array.read arr 0 & \(Ur a, arr) ->
          Array.allocBeside size a arr & \(new, old) ->
            go 0 size old new
  where
    go :: Int -> Int -> Array a %1 -> Array a %1 -> (Array a, Array a)
    go !i !n !old !new
      | i < n =
          Array.read old i & \(Ur a, old) -> DataFlow.do
            -- It must be safe as long as the first argument is the original,
            -- and the latter is the new resource.
            let a' = Unsafe.toLinear (\(!_, !b) -> b) (clone a)
            new <- Array.write new i a'
            go (i + 1) n old new
      | otherwise = (old, new)
{-# INLINE deepCloneArray' #-}

swapTuple :: (a, b) %1 -> (b, a)
{-# INLINE swapTuple #-}
swapTuple (!a, !b) = (b, a)

nubHash :: (Hashable a) => [a] -> [a]
nubHash = go P.mempty
  where
    go !_ [] = []
    go !s (x : xs)
      | HS.member x s = go s xs
      | otherwise = x : go (HS.insert x s) xs

coerceLin :: (Coercible a b) => a %1 -> b
{-# INLINE coerceLin #-}
coerceLin = Unsafe.toLinear \ !a -> coerce a
