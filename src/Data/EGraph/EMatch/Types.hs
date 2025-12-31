{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

module Data.EGraph.EMatch.Types (
  Substitution (..),
  mapMaybeVar,
  lookupVar,
  insertVar,
  singletonVar,
  substPattern,
) where

import Data.Bifunctor qualified as Bi
import Data.Coerce (coerce)
import Data.DList.DNonEmpty qualified as DLNE
import Data.EGraph.Types (EClassId)
import Data.EGraph.Types.Pattern
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (mapMaybe)
import GHC.Generics (Generic)
import Validation

newtype Substitution v = Substitution {substitution :: HashMap v EClassId}
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)
  deriving newtype (Semigroup, Monoid)

mapMaybeVar ::
  forall v v'.
  (Hashable v') => (v -> Maybe v') -> Substitution v -> Substitution v'
{-# INLINE mapMaybeVar #-}
mapMaybeVar f = Substitution . HM.fromList . mapMaybe (\(k, v) -> (,v) <$> f k) . HM.toList . substitution

lookupVar :: forall v. (Hashable v) => v -> Substitution v -> Maybe EClassId
{-# INLINE lookupVar #-}
lookupVar = coerce $ HM.lookup @v @EClassId

insertVar :: forall v. (Hashable v) => v -> EClassId -> Substitution v -> Substitution v
{-# INLINE insertVar #-}
insertVar = coerce $ HM.insert @v @EClassId

singletonVar :: forall v. (Hashable v) => v -> EClassId -> Substitution v
{-# INLINE singletonVar #-}
singletonVar = coerce $ HM.singleton @v @EClassId

substPattern ::
  (Traversable l, Hashable v) =>
  Substitution v ->
  Pattern l v ->
  Validation (NonEmpty v) (Pattern l EClassId)
substPattern sub = Bi.first DLNE.toNonEmpty . go
  where
    go (Metavar v) = case lookupVar v sub of
      Just eclassId -> pure $ Metavar eclassId
      Nothing -> Failure $ DLNE.singleton v
    go (PNode p) = PNode <$> traverse go p
