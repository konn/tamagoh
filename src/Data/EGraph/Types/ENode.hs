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

import Control.Monad.Borrow.Pure (Copyable (..), Share)
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.Foldable qualified as F
import Data.Functor.Classes (Eq1, Ord1, Show1)
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1)
import Data.Unrestricted.Linear (AsMovable)
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Text.Show.Borrowed (AsCopyableShow (..), Display)
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

instance (Copyable1 l) => Copyable (ENode l) where
  copy = ENode . copy1 . coerceShr @_ @(l EClassId)
  {-# INLINE copy #-}

deriving via
  AsCopyableShow (ENode l)
  instance
    (Copyable1 l, Show1 l) =>
    Display (ENode l)

deriving newtype instance (Show1 l) => Show (ENode l)

deriving newtype instance (Eq1 l) => Eq (ENode l)

deriving newtype instance (Ord1 l) => Ord (ENode l)

deriving newtype instance (Hashable1 l) => Hashable (ENode l)

coerceShr :: (Coercible a b) => Share α a %1 -> Share α b
coerceShr = Unsafe.toLinear \ !a -> coerce a

children :: (P.Foldable l) => ENode l -> [EClassId]
children = F.toList P.. unwrap
