{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
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
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Data.Unrestricted.Linear.Lifted (
  Movable1 (..),
  move1,
  genericLiftMove,
  genericMove1,
  GenericMovable1,
  Copyable1 (..),
  copy1,
  GenericCopyable1,
  genericLiftCopy,
  genericCopy1,
) where

import Control.Applicative (Const)
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Coerce (Coercible, coerce)
import Data.Functor.Linear qualified as Data
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.Unrestricted.Linear qualified as Ur
import GHC.Base (Multiplicity (..))
import Prelude.Linear
import Prelude.Linear.Generically qualified as GLC
import Unsafe.Linear qualified as Unsafe

class Movable1 f where
  liftMove :: (a %1 -> Ur b) -> f a %1 -> Ur (f b)

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

genericLiftMove :: forall f a b. (GenericMovable1 f) => (a %1 -> Ur b) -> f a %1 -> Ur (f b)
{-# INLINE genericLiftMove #-}
genericLiftMove f x = GLC.to1 Data.<$> (gliftMove f (GLC.from1 x))

genericMove1 :: forall f a. (GenericMovable1 f, Movable a) => f a %1 -> Ur (f a)
{-# INLINE genericMove1 #-}
genericMove1 = genericLiftMove move

type GMovable1 :: (Type -> Type) -> Constraint
class GMovable1 f where
  gliftMove :: (a %1 -> Ur b) -> f a %1 -> Ur (f b)

instance GMovable1 (GLC.U1 @Type) where
  gliftMove _ GLC.U1 = Ur GLC.U1
  {-# INLINE gliftMove #-}

instance GMovable1 (GLC.V1 @Type) where
  gliftMove _ v1 = case v1 of {}
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f GLC.:*: g) where
  gliftMove f (x GLC.:*: y) = (GLC.:*:) Data.<$> gliftMove f x Data.<*> gliftMove f y
  {-# INLINE gliftMove #-}

instance (GMovable1 f, GMovable1 g) => GMovable1 (f GLC.:+: g) where
  gliftMove f (GLC.L1 x) = GLC.L1 Data.<$> gliftMove f x
  gliftMove f (GLC.R1 y) = GLC.R1 Data.<$> gliftMove f y
  {-# INLINE gliftMove #-}

instance (GMovable1 f) => GMovable1 (GLC.MP1 @Type Many f) where
  gliftMove f (GLC.MP1 c) = GLC.MP1 `Ur.lift` gliftMove f c
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

class Copyable1 f where
  liftCopy :: (Share α a %1 -> b) -> Share α (f a) %1 -> f b

type GenericCopyable1 f = (Copyable1 (GLC.Rep1 @Type f), GLC.Generic1 f)

genericLiftCopy :: forall f a b α. (GenericCopyable1 f) => (Share α a %1 -> b) -> Share α (f a) %1 -> f b
{-# INLINE genericLiftCopy #-}
genericLiftCopy f (UnsafeAlias x) = GLC.to1 $ liftCopy f (UnsafeAlias $ GLC.from1 x)

genericCopy1 :: forall f a α. (GenericCopyable1 f, Copyable a) => Share α (f a) %1 -> f a
{-# INLINE genericCopy1 #-}
genericCopy1 = genericLiftCopy copy

copy1 :: (Copyable1 f, Copyable a) => Share α (f a) %1 -> f a
{-# INLINE copy1 #-}
copy1 = liftCopy copy

instance (GenericCopyable1 f) => Copyable1 (GLC.Generically1 @Type f) where
  liftCopy f = GLC.Generically1 . genericLiftCopy f . coerceShr
  {-# INLINE liftCopy #-}

instance (Copyable c) => Copyable1 (GLC.K1 i c) where
  liftCopy _ = coerce $! copy @c
  {-# INLINE liftCopy #-}

instance Copyable1 GLC.Par1 where
  liftCopy f = GLC.Par1 . f . coerceShr
  {-# INLINE liftCopy #-}

instance (Copyable1 f) => Copyable1 (GLC.M1 i c f) where
  liftCopy f = GLC.M1 . liftCopy f . coerceShr @_ @(f _)
  {-# INLINE liftCopy #-}

instance (Copyable1 l, Copyable1 r) => Copyable1 (l GLC.:*: r) where
  liftCopy f = \(UnsafeAlias (!l GLC.:*: !r)) ->
    let !l' = liftCopy f (UnsafeAlias l)
        !r' = liftCopy f (UnsafeAlias r)
     in l' GLC.:*: r'
  {-# INLINE liftCopy #-}

instance (Copyable1 l, Copyable1 r) => Copyable1 (l GLC.:+: r) where
  liftCopy f = \(UnsafeAlias sum) -> case sum of
    GLC.L1 !l -> GLC.L1 $! (liftCopy f (UnsafeAlias l))
    GLC.R1 !r -> GLC.R1 $! (liftCopy f (UnsafeAlias r))
  {-# INLINE liftCopy #-}

coerceShr :: (Coercible a b) => Share α a %1 -> Share α b
coerceShr = Unsafe.toLinear \ !a -> coerce a
