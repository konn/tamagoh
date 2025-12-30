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
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Control.Monad.Borrow.Pure.Orphans () where

import Control.Functor.Linear qualified as Control
import Data.Functor.Linear qualified as Data
import Data.List.NonEmpty (NonEmpty (..))

instance Data.Functor NonEmpty where
  fmap f (x :| xs) = f x :| Data.fmap f xs
  {-# INLINE fmap #-}

instance Data.Traversable NonEmpty where
  traverse f (x :| xs) = (:|) Control.<$> f x Control.<*> Data.traverse f xs
  {-# INLINE traverse #-}
