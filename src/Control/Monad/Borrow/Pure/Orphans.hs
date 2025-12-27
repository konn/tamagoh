{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Control.Monad.Borrow.Pure.Orphans (
  Movable1 (..),
  move1,
  genericLiftMove,
  genericMove1,
  GenericMovable1,
) where

import Control.Applicative (Const)
import Control.Monad.Borrow.Pure.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Functor.Linear qualified as Data
import Data.HashMap.Internal.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import GHC.Base (Multiplicity (..))
import Prelude.Linear
import Prelude.Linear.Generically qualified as GLC
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

type GenericMovable1 f = (GMovable1 (GLC.Rep1 @Type f), GLC.Generic1 f)

instance
  (GenericMovable1 f) =>
  Movable1 (GLC.Generically1 @Type f)
  where
  liftMove f = Data.fmap GLC.Generically1 . genericLiftMove f . GLC.unGenerically1
  {-# INLINE liftMove #-}

genericLiftMove :: forall f a. (GenericMovable1 f) => (a %1 -> Ur a) -> f a %1 -> Ur (f a)
{-# INLINE genericLiftMove #-}
genericLiftMove f x = GLC.to1 Data.<$> (gliftMove f (GLC.from1 x))

genericMove1 :: forall f a. (GenericMovable1 f, Movable a) => f a %1 -> Ur (f a)
{-# INLINE genericMove1 #-}
genericMove1 = genericLiftMove move

type GMovable1 :: (Type -> Type) -> Constraint
class GMovable1 f where
  gliftMove :: (a %1 -> Ur a) -> f a %1 -> Ur (f a)

instance GMovable1 (GLC.U1 @Type) where
  gliftMove _ GLC.U1 = Ur GLC.U1
  {-# INLINE gliftMove #-}

instance GMovable1 (GLC.V1 @Type) where
  gliftMove _ v1 = case v1 of {}
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f GLC.:*: g) where
  gliftMove f (x GLC.:*: y) = (GLC.:*:) P.<$> gliftMove f x P.<*> gliftMove f y
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f GLC.:+: g) where
  gliftMove f (GLC.L1 x) = GLC.L1 Data.<$> gliftMove f x
  gliftMove f (GLC.R1 y) = GLC.R1 Data.<$> gliftMove f y
  {-# INLINE gliftMove #-}

instance GMovable1 (GLC.MP1 @Type Many f) where
  gliftMove _ (GLC.MP1 c) = Ur (GLC.MP1 c)
  {-# INLINE gliftMove #-}

instance (GMovable1 f) => GMovable1 (GLC.MP1 @Type One f) where
  gliftMove f (GLC.MP1 x) = GLC.MP1 Data.<$> gliftMove f x
  {-# INLINE gliftMove #-}

instance (Movable c) => GMovable1 (GLC.K1 @Type i c) where
  gliftMove _ (GLC.K1 c) = GLC.K1 Data.<$> move c
  {-# INLINE gliftMove #-}

instance GMovable1 GLC.Par1 where
  gliftMove f (GLC.Par1 a) = GLC.Par1 Data.<$> f a
  {-# INLINE gliftMove #-}

instance (GMovable1 f) => GMovable1 (GLC.M1 @Type i c f) where
  gliftMove f (GLC.M1 x) = GLC.M1 Data.<$> gliftMove f x
  {-# INLINE gliftMove #-}

deriving via
  GLC.Generically1 (Const Int)
  instance
    Movable1 (Const Int)

deriving via
  GLC.Generically1 Proxy
  instance
    Movable1 Proxy

deriving via
  GLC.Generically1 Maybe
  instance
    Movable1 Maybe
