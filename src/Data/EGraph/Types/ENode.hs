{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.ENode (ENode (..)) where

import Control.Monad.Borrow.Pure (Copyable (..), DistributesAlias, Share, split)
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.Functor.Classes (Eq1, Ord1, Show1, compare1, eq1, showsPrec1)
import Data.Functor.Linear qualified as Data
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Ord, Show)
import Prelude qualified as P

newtype ENode l = ENode {unwrap :: l EClassId}
  deriving (Generic)

instance (DistributesAlias l, Data.Functor l) => Copyable (ENode l) where
  copy = ENode . Data.fmap copy . split . coerceShr @_ @(l EClassId)
  {-# INLINE copy #-}

instance (Hashable1 l) => Hashable (ENode l) where
  hashWithSalt = coerce P.$ hashWithSalt1 @l @EClassId
  {-# INLINE hashWithSalt #-}

instance (Show1 l) => Show (ENode l) where
  showsPrec = coerce P.$ showsPrec1 @l @EClassId
  {-# INLINE showsPrec #-}

instance (Eq1 l) => Eq (ENode l) where
  (==) = coerce P.$ eq1 @l @EClassId
  {-# INLINE (==) #-}

instance (Ord1 l) => Ord (ENode l) where
  compare = coerce P.$ compare1 @l @EClassId
  {-# INLINE compare #-}

coerceShr :: (Coercible a b) => Share α a %1 -> Share α b
coerceShr = Unsafe.toLinear coerce