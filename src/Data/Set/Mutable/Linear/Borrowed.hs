{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.Set.Mutable.Linear.Borrowed (
  Set,
  empty,
  singleton,
  fromList,
  insert,
  inserts,
  member,
  toList,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Coerce (coerce)
import Data.Linear.Witness.Compat (fromPB)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Set.Mutable.Linear (Keyed)
import Data.Set.Mutable.Linear.Witness qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe

-- NOTE: we need indirection here, because 'Raw.Set' uses Array behind the scenes,
-- and regrows new array. If the our 'Set' is stored in another mutable borrows,
-- then just threading through 'Raw.Set' would discard the change to the outer borrow.
newtype Set k = Set (Ref (Raw.Set k))
  deriving newtype (LinearOnly)

instance Consumable (Set k) where
  consume = \(Set ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

instance Dupable (Set k) where
  dup2 = Unsafe.toLinear \(Set ref) -> DataFlow.do
    (lin, ref) <- withLinearly ref
    (ref, ref2) <- Unsafe.toLinear (\ref -> let (!_, !ref2) = dup $ freeRef ref in (ref, ref2)) ref
    (Set ref, Set $ Ref.new ref2 lin)
  {-# INLINE dup2 #-}

empty :: (Keyed k) => Int -> BO α (Set k)
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    dup l & \(l, l') ->
      Control.pure $ Set $ Ref.new (Raw.emptyL size $ fromPB l) l'

singleton :: (Keyed k) => k %1 -> BO α (Set k)
{-# INLINE singleton #-}
singleton = Unsafe.toLinear \key -> withLinearlyBO \l ->
  dup l & \(l, l') ->
    Control.pure $ Set $ Ref.new (Raw.fromListL [key] $ fromPB l) l'

fromList :: (Keyed k) => [k] %1 -> BO α (Set k)
{-# INLINE fromList #-}
fromList = Unsafe.toLinear \keys -> withLinearlyBO \l ->
  dup l & \(l, l') ->
    Control.pure $ Set $ Ref.new (Raw.fromListL keys $ fromPB l) l'

insert :: (Keyed k) => k %1 -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
{-# INLINE insert #-}
insert = Unsafe.toLinear2 \key set -> Control.do
  set <- modifyRef (\s -> Raw.insert key s) (coerceBor set)
  Control.pure $ recoerceBor set

inserts :: (Keyed k) => [k] %1 -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
{-# INLINE inserts #-}
inserts [] old = Control.pure old
inserts (k : ks) old = Control.do
  old <- insert k old
  inserts ks old

askRaw ::
  (Raw.Set k %1 -> (a, Raw.Set k)) %1 ->
  Borrow bk α (Set k) %1 ->
  BO α a
{-# INLINE askRaw #-}
askRaw f dic = case share dic of
  Ur dic -> Control.do
    UnsafeAlias dic <- readSharedRef (coerceBor dic)
    case f dic of
      (!res, !dic) -> dic `lseq` Control.pure res

askRaw_ ::
  (Raw.Set k %1 -> Ur a) %1 ->
  Borrow bk α (Set k) %1 ->
  BO α a
{-# INLINE askRaw_ #-}
askRaw_ f dic = case share dic of
  Ur dic -> Control.do
    UnsafeAlias dic <- readSharedRef (coerceBor dic)
    case f dic of
      Ur !res -> Control.pure res

member ::
  forall k α.
  (Keyed k) =>
  k ->
  Share α (Set k) %1 ->
  BO α (Ur Bool)
{-# INLINE member #-}
member key set = askRaw (Raw.member key) set

toList :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α [k]
{-# INLINE toList #-}
toList set = askRaw_ Raw.toList set

coerceBor ::
  forall k bk α.
  Borrow bk α (Set k) %1 ->
  Borrow bk α (Ref (Raw.Set k))
{-# INLINE coerceBor #-}
coerceBor = Unsafe.toLinear coerce

recoerceBor ::
  forall k bk α.
  Borrow bk α (Ref (Raw.Set k)) %1 ->
  Borrow bk α (Set k)
{-# INLINE recoerceBor #-}
recoerceBor = Unsafe.toLinear coerce
