{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Linear.Witness.Compat (fromPB, fromLE) where

import Control.Monad.Borrow.Pure.Lifetime.Token.Internal (LinearOnly (..), LinearOnlyWitness (..))
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal qualified as PB
import Linear.Witness.Token.Internal qualified as LE
import Linear.Witness.Token.Unsafe (HasLinearWitness)
import Unsafe.Linear qualified as Unsafe

instance LinearOnly LE.Linearly where
  linearOnly = UnsafeLinearOnly

instance HasLinearWitness PB.Linearly

fromPB :: PB.Linearly %1 -> LE.Linearly
{-# INLINE fromPB #-}
fromPB = Unsafe.toLinear \_ -> LE.Linearly

fromLE :: LE.Linearly %1 -> PB.Linearly
{-# INLINE fromLE #-}
fromLE = Unsafe.toLinear \_ -> PB.UnsafeLinearly
