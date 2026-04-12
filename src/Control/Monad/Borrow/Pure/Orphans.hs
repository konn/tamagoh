{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
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
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Control.Monad.Borrow.Pure.Orphans () where

import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Data.Array.Mutable.Linear qualified as LA
import Data.Semigroup qualified as Sem
import Data.Strict.Maybe qualified as Strict
import Data.Vector.Mutable.Linear qualified as LV
import Prelude.Linear
import Prelude.Linear.Generically

deriving newtype instance (Dupable a) => Dupable (Sem.Min a)

deriving newtype instance (Movable a) => Movable (Sem.Min a)

deriving via Generically (Sem.Arg a b) instance (Dupable a, Dupable b) => Dupable (Sem.Arg a b)

deriving via Generically (Sem.Arg a b) instance (Movable a, Movable b) => Movable (Sem.Arg a b)

instance (Consumable a) => Consumable (Strict.Maybe a) where
  consume Strict.Nothing = ()
  consume (Strict.Just x) = consume x
  {-# INLINE consume #-}

instance (Dupable a) => Dupable (Strict.Maybe a) where
  dup2 Strict.Nothing = (Strict.Nothing, Strict.Nothing)
  dup2 (Strict.Just x) =
    let %1 !(x1, x2) = dup2 x
     in (Strict.Just x1, Strict.Just x2)
  {-# INLINE dup2 #-}

instance LinearOnly (LV.Vector a) where
  linearOnly = UnsafeLinearOnly

instance LinearOnly (LA.Array a) where
  linearOnly = UnsafeLinearOnly
