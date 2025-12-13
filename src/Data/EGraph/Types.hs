{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types (EGraph, find) where

import Control.Syntax.DataFlow qualified as DataFlow
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1, Ord1, Show1, compare1, eq1, showsPrec1)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (HashMap)
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import Data.Set.Mutable.Linear
import Data.UnionFind.Linear (Key, UnionFind)
import Data.UnionFind.Linear qualified as UF
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find)
import Prelude (Eq (..), Ord, Show)
import Prelude qualified as P

newtype EClassId = EClassId {getEClassId :: Key}
  deriving (Eq, Ord, Generic)
  deriving newtype (Show, Hashable, Consumable, Dupable, Movable)

newtype ENode f = ENode {app :: f EClassId}
  deriving (Generic)

instance (Hashable1 f) => Hashable (ENode f) where
  hashWithSalt = coerce P.$ hashWithSalt1 @f @EClassId
  {-# INLINE hashWithSalt #-}

instance (Show1 f) => Show (ENode f) where
  showsPrec = coerce P.$ showsPrec1 @f @EClassId
  {-# INLINE showsPrec #-}

instance (Eq1 f) => Eq (ENode f) where
  (==) = coerce P.$ eq1 @f @EClassId
  {-# INLINE (==) #-}

instance (Ord1 f) => Ord (ENode f) where
  compare = coerce P.$ compare1 @f @EClassId
  {-# INLINE compare #-}

data EGraph f = EGraph
  { unionFind :: !UnionFind
  , classes :: !(HashMap EClassId (Set (ENode f)))
  , hashcons :: !(HashMap (ENode f) EClassId)
  }
  deriving (Generic)

find :: EGraph f %1 -> EClassId -> (Ur (Maybe EClassId), EGraph f)
find EGraph {..} (EClassId k) = DataFlow.do
  (k', unionFind) <- UF.find k unionFind
  (Data.fmap EClassId Data.<$> k', EGraph {..})
