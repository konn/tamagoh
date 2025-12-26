{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}

module Data.EGraph.Types.EClassId (EClassId (..)) where

import Control.Monad.Borrow.Pure (Copyable)
import Data.Hashable
import Data.UnionFind.Linear (Key)
import Data.Unrestricted.Linear qualified as PL
import GHC.Generics (Generic)
import Prelude.Linear qualified as PL

newtype EClassId = EClassId {getKey :: Key}
  deriving (Eq, Ord, Generic)
  deriving newtype
    ( PL.Eq
    , PL.Ord
    , Show
    , Hashable
    , PL.Consumable
    , PL.Dupable
    , PL.Movable
    , Copyable
    )
