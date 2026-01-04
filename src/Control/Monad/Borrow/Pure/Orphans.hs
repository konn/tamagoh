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

import Control.Functor.Linear qualified as Control
import Data.Functor.Linear qualified as Data
import Data.List.NonEmpty (NonEmpty (..))
import Data.Semigroup qualified as Sem
import Prelude.Linear
import Prelude.Linear.Generically

instance Data.Functor NonEmpty where
  fmap f (x :| xs) = f x :| Data.fmap f xs
  {-# INLINE fmap #-}

instance Data.Traversable NonEmpty where
  traverse f (x :| xs) = (:|) Control.<$> f x Control.<*> Data.traverse f xs
  {-# INLINE traverse #-}

deriving newtype instance (Dupable a) => Dupable (Sem.Min a)

deriving newtype instance (Movable a) => Movable (Sem.Min a)

deriving via Generically (Sem.Arg a b) instance (Dupable a, Dupable b) => Dupable (Sem.Arg a b)

deriving via Generically (Sem.Arg a b) instance (Movable a, Movable b) => Movable (Sem.Arg a b)
