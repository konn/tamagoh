{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Control.Monad.Borrow.Pure.Orphans (
  Movable1 (..),
  move1,
  genericLiftMove,
  genericMove1,
  GenericMovable1,
) where

import Control.Monad.Borrow.Pure.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Functor.Linear qualified as Data
import Data.HashMap.Internal.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import GHC.Base (Multiplicity (..))
import Prelude.Linear
import Prelude.Linear.Generically
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

instance (Copyable a) => Copyable (HashSet a) where
  copy = \(UnsafeAlias hs) -> hs
  {-# INLINE copy #-}

instance (Copyable k, Copyable v) => Copyable (HashMap k v) where
  copy = \(UnsafeAlias hs) -> hs
  {-# INLINE copy #-}

instance (Consumable a) => Consumable (HashSet a) where
  consume = consume . Unsafe.toLinear HashSet.toList
  {-# INLINE consume #-}

instance (Dupable a, Hashable a) => Dupable (HashSet a) where
  dup2 hs = DataFlow.do
    hs <- Unsafe.toLinear HashSet.toList hs
    (hs1, hs2) <- dup hs
    (Unsafe.toLinear HashSet.fromList hs1, Unsafe.toLinear HashSet.fromList hs2)
  {-# INLINE dup2 #-}

class Movable1 f where
  liftMove :: (a %1 -> Ur a) -> f a %1 -> Ur (f a)

move1 :: (Movable1 f, Movable a) => f a %1 -> Ur (f a)
{-# INLINE move1 #-}
move1 = liftMove move

type GenericMovable1 f = (GMovable1 (Rep1 f), Generic1 f)

instance (GenericMovable1 f) => Movable1 (Generically1 f) where
  liftMove f = Data.fmap Generically1 . genericLiftMove f . unGenerically1
  {-# INLINE liftMove #-}

genericLiftMove :: forall f a. (GenericMovable1 f) => (a %1 -> Ur a) -> f a %1 -> Ur (f a)
{-# INLINE genericLiftMove #-}
genericLiftMove f x = to1 Data.<$> (gliftMove f (from1 x))

genericMove1 :: forall f a. (GenericMovable1 f, Movable a) => f a %1 -> Ur (f a)
{-# INLINE genericMove1 #-}
genericMove1 = genericLiftMove move

class GMovable1 f where
  gliftMove :: (a %1 -> Ur a) -> f a %1 -> Ur (f a)

instance GMovable1 U1 where
  gliftMove _ U1 = Ur U1
  {-# INLINE gliftMove #-}

instance GMovable1 V1 where
  gliftMove _ v1 = case v1 of {}
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f :*: g) where
  gliftMove f (x :*: y) = (:*:) P.<$> gliftMove f x P.<*> gliftMove f y
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f :+: g) where
  gliftMove f (L1 x) = L1 Data.<$> gliftMove f x
  gliftMove f (R1 y) = R1 Data.<$> gliftMove f y
  {-# INLINE gliftMove #-}

instance GMovable1 (MP1 Many f) where
  gliftMove _ (MP1 c) = Ur (MP1 c)
  {-# INLINE gliftMove #-}

instance (Movable1 f) => GMovable1 (MP1 One f) where
  gliftMove f (MP1 x) = MP1 Data.<$> liftMove f x
  {-# INLINE gliftMove #-}

instance (Movable c) => GMovable1 (K1 i c) where
  gliftMove _ (K1 c) = K1 Data.<$> move c
  {-# INLINE gliftMove #-}

instance GMovable1 Par1 where
  gliftMove f (Par1 a) = Par1 Data.<$> f a
  {-# INLINE gliftMove #-}

instance (GMovable1 f) => Movable1 (M1 i t f) where
  liftMove f (M1 x) = M1 Data.<$> gliftMove f x
  {-# INLINE liftMove #-}