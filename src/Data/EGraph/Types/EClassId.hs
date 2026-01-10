{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}

module Data.EGraph.Types.EClassId (EClassId (..), idToWord) where

import Control.Monad.Borrow.Pure (Copyable)
import Data.Coerce (coerce)
import Data.Hashable
import Data.UnionFind.Linear (Key (..))
import Data.Unrestricted.Linear qualified as PL
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Unboxed qualified as U
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
  deriving newtype (U.Unbox, G.Vector U.Vector, MG.MVector U.MVector)

newtype instance U.Vector EClassId = V_Eid (U.Vector Key)

newtype instance U.MVector s EClassId = MV_Eid (U.MVector s Key)

instance Show EClassId where
  showsPrec d (EClassId k) =
    showParen (d > 10) $
      showString "EClassId " . showsPrec 11 k

idToWord :: EClassId -> PL.Word
idToWord = coerce
