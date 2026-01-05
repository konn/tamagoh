{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Tamagoh.Bench.Orphans () where

import Data.Equality.Saturation qualified as Hegg
import Data.Functor.Foldable

type instance Base (Hegg.Fix f) = f

instance (Functor f) => Recursive (Hegg.Fix f) where
  project (Hegg.Fix x) = x
  {-# INLINE project #-}

instance (Functor f) => Corecursive (Hegg.Fix f) where
  embed = Hegg.Fix
  {-# INLINE embed #-}
