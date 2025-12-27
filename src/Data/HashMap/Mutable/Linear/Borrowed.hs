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
  fromList,
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
  swap,
  take,
  take_,
  union,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.HashSet qualified as IHS
import Data.Linear.Witness.Compat (fromPB)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- NOTE: we need indirection here, because 'Raw.HashMap' uses Array behind the scenes,
-- and regrows new array. If the our 'HashMap' is stored in another mutable borrows,
-- then just threading through 'Raw.HashMap' would discard the change to the outer borrow.
newtype HashMap k v = HM (Ref (Raw.HashMap k v))
  deriving newtype (LinearOnly)

inner :: HashMap k v %1 -> Ref (Raw.HashMap k v)
{-# INLINE inner #-}
inner = Unsafe.toLinear coerce

instance Consumable (HashMap k v) where
  consume = \(HM ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

instance Dupable (HashMap k v) where
  dup2 = Unsafe.toLinear \(HM ref) -> DataFlow.do
    (lin, ref) <- withLinearly ref
    (ref, ref2) <- Unsafe.toLinear (\ref -> let (!_, !ref2) = dup $ freeRef ref in (ref, ref2)) ref
    (HM ref, HM $ Ref.new ref2 lin)
  {-# INLINE dup2 #-}

empty :: forall k v. (Keyed k) => Int -> Linearly %1 -> HashMap k v
{-# INLINE empty #-}
empty size l =
  dup l & \(l, l'') -> HM $ Ref.new (Raw.emptyL size $ fromPB l) l''

fromList :: (Keyed k) => [(k, v)] %1 -> Linearly %1 -> HashMap k v
{-# INLINE fromList #-}
fromList = Unsafe.toLinear \keys -> \l ->
  dup l & \(l, l') ->
    HM $ Ref.new (Raw.fromListL keys $ fromPB l) l'

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

askRaw_ ::
  (Raw.HashMap k v %1 -> Ur a) %1 ->
  Borrow bk α (HashMap k v) %1 ->
  BO α a
{-# INLINE askRaw_ #-}
askRaw_ f dic = case share dic of
  Ur dic -> Control.do
    UnsafeAlias dic <- readSharedRef (coerceBor dic)
    case f dic of
      Ur !res -> Control.pure res

toList :: Borrow bk α (HashMap k v) %1 -> BO α [(k, v)]
{-# INLINE toList #-}
toList = askRaw_ Raw.toList

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

swap ::
  forall k v α.
  HashMap k v %1 ->
  Mut α (HashMap k v) %1 ->
  BO α (HashMap k v, Mut α (HashMap k v))
{-# INLINE swap #-}
swap keys dic = withLinearlyBO \lin -> Control.do
  Bi.second recoerceBor
    Control.<$> updateRef (\old -> Control.pure (HM $ Ref.new old lin, freeRef $ inner keys)) (coerceBor dic)

-- | Takes all elements from the set, leaving it empty.
take :: forall k v α. (Keyed k) => Mut α (HashMap k v) %1 -> BO α (HashMap k v, Mut α (HashMap k v))
{-# INLINE take #-}
take set = Control.do
  Bi.second recoerceBor Control.<$> updateRef go (coerceBor set)
  where
    go :: Raw.HashMap k v %1 -> BO α (HashMap k v, Raw.HashMap k v)
    {-# INLINE go #-}
    go = \s -> withLinearlyBO \lin ->
      dup lin & \(lin, lin') -> Control.do
        Control.pure (HM $ Ref.new s lin, Raw.emptyL 16 $ fromPB lin')

take_ :: forall k v α. (Keyed k) => Mut α (HashMap k v) %1 -> BO α (HashMap k v)
{-# INLINE take_ #-}
take_ set = Control.fmap (uncurry $ flip lseq) $ take set

union :: (Keyed k) => HashMap k v %1 -> HashMap k v %1 -> HashMap k v
{-# INLINE union #-}
union (HM ref1) (HM ref2) = DataFlow.do
  (l, ref1) <- withLinearly ref1
  HM $ Ref.new (Raw.union (freeRef ref1) (freeRef ref2)) l
