{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.Mutable.Linear.Borrowed (
  HashMap,
  Keyed,
  empty,
  insert,
  delete,
  shrinkToFit,
  alter,
  alterF,
  size,
  capacity,
  lookup,
  lookups,
  member,
  toList,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Coerce (coerce)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.HashSet qualified as IHS
import Data.Linear.Witness.Compat (fromPB)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- NOTE: we need indirection here, because 'Raw.HashMap' uses Array behind the scenes,
-- and regrows new array. If the our 'HashMap' is stored in another mutable borrows,
-- then just threading through 'Raw.HashMap' would discard the change to the outer borrow.
newtype HashMap k v = HM (Ref (Raw.HashMap k v))

inner :: HashMap k v %1 -> Ref (Raw.HashMap k v)
{-# INLINE inner #-}
inner = Unsafe.toLinear coerce

instance Consumable (HashMap k v) where
  consume = \(HM ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

empty :: (Keyed k) => Int -> BO α (Mut α (HashMap k v), Lend α (HashMap k v))
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    dup3 l & \(l, l', l'') -> Control.do
      Control.pure $ borrow (HM $ Ref.new (Raw.emptyL size $ fromPB l) l'') l'

-- TODO: more efficient implementation
insert ::
  (Keyed k) =>
  k ->
  v %1 ->
  Mut α (HashMap k v) %1 ->
  BO α (Maybe v, Mut α (HashMap k v))
{-# NOINLINE insert #-}
insert key = Unsafe.toLinear2 \v dic -> Control.do
  (mold, dic) <- delete key dic
  dic <- modifyRef (\dic -> Raw.insert key v dic) (coerceBor dic)
  Control.pure (mold, recoerceBor dic)

-- TODO: more efficient implementation
delete ::
  (Keyed k) => k -> Mut α (HashMap k v) %1 -> BO α (Maybe v, Mut α (HashMap k v))
{-# NOINLINE delete #-}
delete key dic = Control.do
  (mval, dic) <-
    updateRef
      ( \dic -> case Raw.lookup key dic of
          (!(Ur !(Just !v)), !dic) -> case Raw.delete key dic of
            !dic -> Control.pure (Just v, dic)
          (!(Ur Nothing), !dic) -> Control.pure (Nothing, dic)
      )
      (coerceBor dic)
  Control.pure (mval, recoerceBor dic)

shrinkToFit ::
  forall k v α.
  (Keyed k) => Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE shrinkToFit #-}
shrinkToFit =
  Control.fmap recoerceBor
    . modifyRef Raw.shrinkToFit
    . coerceBor

alter ::
  (Keyed k) =>
  (Maybe v %1 -> Maybe v) ->
  k ->
  Mut α (HashMap k v) %1 ->
  BO α (Mut α (HashMap k v))
{-# INLINE alter #-}
alter f k =
  Control.fmap recoerceBor
    . modifyRef (Raw.alter (Unsafe.toLinear f) k)
    . coerceBor

alterF ::
  (Keyed k) =>
  (Maybe v %1 -> BO α (Maybe v)) ->
  k ->
  Mut α (HashMap k v) %1 ->
  BO α (Mut α (HashMap k v))
{-# INLINE alterF #-}
alterF f key dic = Control.do
  ((), dic) <-
    updateRef
      ( Control.fmap ((),)
          . Raw.alterF (Control.fmap (Unsafe.toLinear Ur) . Unsafe.toLinear f) key
      )
      (coerceBor dic)
  Control.pure $ recoerceBor dic

askRaw ::
  (Raw.HashMap k v %1 -> (a, Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMap k v) %1 ->
  BO α a
{-# INLINE askRaw #-}
askRaw f dic = case share dic of
  Ur dic -> Control.do
    UnsafeAlias dic <- readSharedRef (coerceBor dic)
    case f dic of
      (!res, !dic) -> dic `lseq` Control.pure res

size :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE size #-}
size = askRaw Raw.size

capacity :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE capacity #-}
capacity = askRaw Raw.capacity

lookup ::
  (Keyed k) =>
  k ->
  Borrow bk α (HashMap k v) %1 ->
  BO α (Maybe (Borrow bk α v))
{-# INLINE lookup #-}
lookup key dic = Control.do
  Data.fmap UnsafeAlias . unur Control.<$> askRaw (Raw.lookup key) dic

lookups ::
  (Keyed k) =>
  [k] ->
  Borrow bk α (HashMap k v) %1 ->
  BO α [(Ur k, (Maybe (Borrow bk α v)))]
{-# INLINE lookups #-}
lookups keys0 = Unsafe.toLinear \dic -> Control.do
  let keys = P.map Ur $ IHS.toList $ IHS.fromList keys0
  Data.forM keys (\(Ur !key) -> lookup key dic Control.<&> \ !v -> (Ur key, v))

member :: (Keyed k) => k -> Borrow bk α (HashMap k v) %1 -> BO α (Ur Bool)
{-# INLINE member #-}
member key = askRaw (Raw.member key)

toList :: Lend α (HashMap k v) %1 -> End α -> [(k, v)]
{-# INLINE toList #-}
toList lend end = unur $ Raw.toList $ freeRef $ inner $ reclaim lend end

coerceBor ::
  forall k v bk α.
  Borrow bk α (HashMap k v) %1 ->
  Borrow bk α (Ref (Raw.HashMap k v))
{-# INLINE coerceBor #-}
coerceBor = Unsafe.toLinear coerce

recoerceBor ::
  forall k v bk α.
  Borrow bk α (Ref (Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMap k v)
{-# INLINE recoerceBor #-}
recoerceBor = Unsafe.toLinear coerce
