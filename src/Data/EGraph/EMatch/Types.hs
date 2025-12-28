{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

module Data.EGraph.EMatch.Types (Substitution (..), lookupVar, insertVar) where

import Data.Coerce (coerce)
import Data.EGraph.Types (EClassId)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

newtype Substitution v = Substitution {substitution :: HashMap v EClassId}
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)
  deriving newtype (Semigroup, Monoid)

lookupVar :: forall v. (Hashable v) => v -> Substitution v -> Maybe EClassId
{-# INLINE lookupVar #-}
lookupVar = coerce $ HM.lookup @v @EClassId

insertVar :: forall v. (Hashable v) => v -> EClassId -> Substitution v -> Substitution v
{-# INLINE insertVar #-}
insertVar = coerce $ HM.insert @v @EClassId