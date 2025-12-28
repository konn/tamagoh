{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EGraph.Types.Language (
  Language,
  Term,
  wrapTerm,
  unwrapTerm,
  Matchable (..),
  GenericMatchable,
  genericTryMatch,
) where

import Control.Monad (guard)
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Data.Coerce (coerce)
import Data.FMList (FMList)
import Data.FMList qualified as FML
import Data.Fix
import Data.Hashable.Lifted (Hashable1)
import Data.Kind
import Data.Traversable qualified as P
import GHC.Generics
import GHC.Generics qualified as GHC
import Generics.Linear

type Language l = (Hashable1 l, Movable1 l, P.Traversable l, Matchable l)

type Term l = Fix l

wrapTerm :: l (Term l) -> Term l
wrapTerm = Fix

unwrapTerm :: Term l -> l (Term l)
unwrapTerm (Fix l) = l

type GenericMatchable f = (GHC.Generic1 f, Matchable (GHC.Rep1 f))

genericTryMatch :: (GenericMatchable f) => f a -> f b -> Maybe (FMList (a, b))
{-# INLINE genericTryMatch #-}
genericTryMatch = (. GHC.from1) . tryMatch . GHC.from1

instance (GenericMatchable f) => Matchable (Generically1 f) where
  tryMatch ::
    forall a b.
    Generically1 f a ->
    Generically1 f b ->
    Maybe (FMList (a, b))
  tryMatch = coerce $ genericTryMatch @f @a @b

type Matchable :: (Type -> Type) -> Constraint
class Matchable l where
  tryMatch :: l a -> l b -> Maybe (FMList (a, b))

instance Matchable U1 where
  tryMatch = \_ _ -> Just mempty
  {-# INLINE tryMatch #-}

instance Matchable V1 where
  tryMatch = \case {}
  {-# INLINE tryMatch #-}

instance (Matchable l, Matchable r) => Matchable (l :*: r) where
  {-# INLINE tryMatch #-}
  tryMatch = \(l1 :*: r1) (l2 :*: r2) ->
    (<>) <$> tryMatch l1 l2 <*> tryMatch r1 r2

instance (Matchable l, Matchable r) => Matchable (l :+: r) where
  tryMatch = \cases
    (L1 x) (L1 y) -> tryMatch x y
    (R1 x) (R1 y) -> tryMatch x y
    _ _ -> Nothing
  {-# INLINE tryMatch #-}

instance (Eq c) => Matchable (K1 i c) where
  tryMatch = \(K1 c1) (K1 c2) -> mempty <$ guard (c1 == c2)
  {-# INLINE tryMatch #-}

instance (Matchable f) => Matchable (M1 i t f) where
  tryMatch :: forall a b. M1 i t f a -> M1 i t f b -> Maybe (FMList (a, b))
  tryMatch = coerce $ tryMatch @f @a @b
  {-# INLINE tryMatch #-}

instance (Matchable f) => Matchable (Rec1 f) where
  tryMatch :: forall a b. Rec1 f a -> Rec1 f b -> Maybe (FMList (a, b))
  tryMatch = coerce $ tryMatch @f @a @b
  {-# INLINE tryMatch #-}

instance (Matchable f) => Matchable (MP1 m f) where
  tryMatch = \(MP1 x) (MP1 y) -> tryMatch x y
  {-# INLINE tryMatch #-}

instance Matchable Par1 where
  tryMatch :: forall a b. Par1 a -> Par1 b -> Maybe (FMList (a, b))
  tryMatch = coerce $ fmap (Just . FML.singleton) . (,) @a @b
  {-# INLINE tryMatch #-}
