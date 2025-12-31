{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Monad.Borrow.Pure.Freeze (
  -- * Basic Operations
  freeze,
  thaw,

  -- * Internals
  Freeze (..),

  -- * Unsafe Operations
  unsafeThaw,
) where

import Control.Monad.Borrow.Pure
import Prelude.Linear
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe

-- NOTE: We really miss linear constraints here...
-- ... meanwhile we need O(N) for nested containers...

class Freeze linear frozen | linear -> frozen, frozen -> linear where
  {- |
  Freeze a linear value into a frozen value.
  This function is for implementation. Use 'freeze' for usage.

  Assumed complexity: \(O(1)\)
  -}
  basicFreeze :: linear %1 -> Ur frozen

  {- | Unsafely thaw a frozen value back into a linear value, without cloning.
  This function is for implementation. Use 'freeze' for usage.

  WARNING: The caller MUST ensure that the frozen value is not used after 'unsafeThaw'.

  Assumed complexity: \(O(1)\)
  -}
  basicUnsafeThaw :: frozen -> Linearly %1 -> linear

-- | \(O(1)\) freezes a linear value into a frozen value.
freeze :: forall linear frozen. (Freeze linear frozen) => linear %1 -> Ur frozen
{-# INLINE [1] freeze #-}
freeze = basicFreeze

{- |
\(O(1)\) unsafely thaws a frozen value back into a linear value.

WARNING: The caller MUST ensure that the frozen value is not used after 'unsafeThaw'.
Use 'thaw' if you want to keep using the frozen value.
-}
unsafeThaw ::
  forall frozen linear.
  (Freeze linear frozen) => frozen -> Linearly %1 -> linear
{-# INLINE [1] unsafeThaw #-}
unsafeThaw = basicUnsafeThaw

thaw ::
  forall frozen linear.
  (Freeze linear frozen, Dupable linear) =>
  frozen -> Linearly %1 -> linear
{-# INLINE [1] thaw #-}
thaw frozen lin =
  (dup $! basicUnsafeThaw frozen lin) PL.& Unsafe.toLinear \(!_, !l') -> l'

{-# RULES
"freeze/thaw" forall xs l.
  freeze (thaw xs l) =
    Ur xs
"freeze/unsafeThaw" forall xs l.
  freeze (unsafeThaw xs l) =
    Ur xs
  #-}
