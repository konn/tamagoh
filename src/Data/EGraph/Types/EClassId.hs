{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Data.EGraph.Types.EClassId (EClassId (..), idToWord) where

import Control.Monad.Borrow.Pure (Copyable)
import Data.Coerce (coerce)
import Data.Hashable
import Data.UnionFind.Linear (Key (..))
import Data.Unrestricted.Linear qualified as PL
import GHC.Generics (Generic)
import Prelude.Linear qualified as PL
import Text.Show.Borrowed (AsCopyableShow (..), Display)

newtype EClassId = EClassId {getKey :: Key}
  deriving (Eq, Ord, Show, Generic)
  deriving newtype
    ( PL.Eq
    , PL.Ord
    , Hashable
    , PL.Consumable
    , PL.Dupable
    , PL.Movable
    , Copyable
    )
  deriving (Display) via AsCopyableShow EClassId

idToWord :: EClassId -> PL.Word
idToWord = coerce
