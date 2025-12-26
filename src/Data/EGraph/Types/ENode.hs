{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.ENode (ENode (..), children) where

import Control.Monad.Borrow.Pure (Copyable (..), DistributesAlias, Share, split)
import Control.Monad.Borrow.Pure.Orphans (Movable1, move1)
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.Foldable qualified as F
import Data.Functor.Classes (Eq1, Ord1, Show1, compare1, eq1, showsPrec1)
import Data.Functor.Linear qualified as Data
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import Data.Unrestricted.Linear (AsMovable)
import Data.Unrestricted.Linear qualified as Ur
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Ord, Show)
import Prelude qualified as P

newtype ENode l = ENode {unwrap :: l EClassId}
  deriving (GHC.Generic)

deriveGeneric ''ENode

deriving via AsMovable (ENode l) instance (Movable1 l) => Consumable (ENode l)

deriving via AsMovable (ENode l) instance (Movable1 l) => Dupable (ENode l)

instance (Movable1 l) => Movable (ENode l) where
  move (ENode l) = Ur.lift ENode (move1 l)
  {-# INLINE move #-}

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

children :: (P.Foldable l) => ENode l -> [EClassId]
children = F.toList P.. unwrap
