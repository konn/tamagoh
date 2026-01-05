{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Tamagoh.Bench.Orphans () where

import Control.DeepSeq (NFData, NFData1)
import Data.Equality.Matching.Pattern qualified as Hegg
import Data.Equality.Saturation qualified as Hegg
import Data.Functor.Foldable
import GHC.Generics (Generic)

type instance Base (Hegg.Fix f) = f

instance (Functor f) => Recursive (Hegg.Fix f) where
  project (Hegg.Fix x) = x
  {-# INLINE project #-}

instance (Functor f) => Corecursive (Hegg.Fix f) where
  embed = Hegg.Fix
  {-# INLINE embed #-}

deriving stock instance Generic (Hegg.Rewrite f a)

deriving stock instance Generic (Hegg.Pattern f)

deriving stock instance Generic (Hegg.Fix f)

deriving anyclass instance (NFData1 f) => NFData (Hegg.Pattern f)

deriving anyclass instance (NFData1 f) => NFData (Hegg.Rewrite a f)

deriving anyclass instance (NFData1 f) => NFData (Hegg.Fix f)
