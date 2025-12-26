{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Control.Monad.Borrow.Pure.Orphans () where

import Control.Monad.Borrow.Pure.Internal
import Data.HashMap.Internal.Strict (HashMap)
import Data.HashSet (HashSet)

instance (Copyable a) => Copyable (HashSet a) where
  copy = \(UnsafeAlias hs) -> hs
  {-# INLINE copy #-}

instance (Copyable k, Copyable v) => Copyable (HashMap k v) where
  copy = \(UnsafeAlias hs) -> hs
  {-# INLINE copy #-}
