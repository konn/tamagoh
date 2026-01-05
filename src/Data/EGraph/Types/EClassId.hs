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
  deriving (Eq, Ord, Generic)
  deriving newtype
    ( PL.Eq
    , PL.Ord
    , Num
    , Enum
    , Integral
    , Real
    , Hashable
    , PL.Consumable
    , PL.Dupable
    , PL.Movable
    , Copyable
    )
  deriving (Display) via AsCopyableShow EClassId

instance Show EClassId where
  showsPrec d (EClassId k) =
    showParen (d > 10) $
      showString "EClassId " . showsPrec 11 k

idToWord :: EClassId -> PL.Word
idToWord = coerce
