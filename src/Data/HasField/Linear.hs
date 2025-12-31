{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Data.HasField.Linear (RecordLabel (), (.#)) where

import Control.Monad.Borrow.Pure.Internal
import GHC.Base (TYPE, Type)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (Symbol)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe

type RecordLabel :: TYPE rep -> Symbol -> Type -> Type
data RecordLabel r field a = RecLab

instance (HasField field r a, field ~ field') => IsLabel field (RecordLabel r field' a) where
  fromLabel = RecLab
  {-# INLINE fromLabel #-}

-- | Subdivides a borrow of a record type @r@ into one of its field @field@.
(.#) ::
  forall field r a k α.
  (HasField field r a) =>
  Borrow k α r %1 ->
  RecordLabel r field a ->
  Borrow k α a
UnsafeAlias !r .# _ = UnsafeAlias $! Unsafe.toLinear (getField @field @r @a) r

infixl 9 .#
