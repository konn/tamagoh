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
  null,
  size,
  toList,
  toListUnborrowed,
  take,
  take_,
  swap,
  union,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.Functor.Linear qualified as Data
import Data.Linear.Witness.Compat (fromPB)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Set.Mutable.Linear (Keyed)
import Data.Set.Mutable.Linear.Witness qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, null, take)
import Unsafe.Linear qualified as Unsafe

-- NOTE: we need indirection here, because 'Raw.Set' uses Array behind the scenes,
-- and regrows new array. If the our 'Set' is stored in another mutable borrows,
-- then just threading through 'Raw.Set' would discard the change to the outer borrow.
newtype Set k = Set (Ref (Raw.Set k))
  deriving newtype (LinearOnly)

inner :: Set k %1 -> Ref (Raw.Set k)
{-# INLINE inner #-}
inner = coerceLin

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

toListUnborrowed :: (Keyed k) => Set k %1 -> [k]
{-# INLINE toListUnborrowed #-}
toListUnborrowed (Set ref) = unur $ Raw.toList (freeRef ref)

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

null :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α (Ur Bool)
{-# INLINE null #-}
null set = askRaw (Bi.first (Data.fmap (== 0)) . Raw.size) set

size :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α (Ur Int)
{-# INLINE size #-}
size = askRaw Raw.size

-- | Takes all elements from the set, leaving it empty.
take :: forall k α. (Keyed k) => Mut α (Set k) %1 -> BO α (Set k, Mut α (Set k))
{-# INLINE take #-}
take set = Control.do
  Bi.second recoerceBor Control.<$> updateRef go (coerceBor set)
  where
    go :: Raw.Set k %1 -> BO α (Set k, Raw.Set k)
    {-# INLINE go #-}
    go = \s -> withLinearlyBO \lin ->
      dup lin & \(lin, lin') -> Control.do
        Control.pure (Set $ Ref.new s lin, Raw.emptyL 16 $ fromPB lin')

take_ :: forall k α. (Keyed k) => Mut α (Set k) %1 -> BO α (Set k)
{-# INLINE take_ #-}
take_ = Control.fmap (uncurry $ flip lseq) . take

swap ::
  forall k α.
  Set k %1 ->
  Mut α (Set k) %1 ->
  BO α (Set k, Mut α (Set k))
{-# INLINE swap #-}
swap keys dic = withLinearlyBO \lin -> Control.do
  Bi.second recoerceBor
    Control.<$> updateRef (\old -> Control.pure (Set $ Ref.new old lin, freeRef $ inner keys)) (coerceBor dic)

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear coerce

union :: (Keyed k) => Set k %1 -> Set k %1 -> Set k
{-# INLINE union #-}
union (Set set1) (Set set2) = DataFlow.do
  (l, set1) <- withLinearly set1
  Set $ Ref.new (Raw.union (freeRef set1) (freeRef set2)) l
