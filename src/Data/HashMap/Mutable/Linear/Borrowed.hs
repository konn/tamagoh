{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.HashMap.Mutable.Linear.Borrowed (
  HashMap,
  Keyed,
  empty,
  fromList,
  insert,
  insertAll,
  delete,
  filter,
  filterWithKey,
  mapMaybe,
  mapMaybeWithKey,
  shrinkToFit,
  alter,
  alterF,
  size,
  capacity,
  lookup,
  member,
  toList,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.HashMap.Mutable.Linear (HashMap, Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.Linear.Witness.Compat (fromPB)
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe

empty :: (Keyed k) => Int -> BO α (Mut α (HashMap k v), Lend α (HashMap k v))
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    dup l & \(l, l') -> Control.do
      Control.pure $ borrow (Raw.emptyL size $ fromPB l) l'

fromList :: (Keyed k) => [(k, v)] -> BO α (Mut α (HashMap k v), Lend α (HashMap k v))
{-# INLINE fromList #-}
fromList kvs = Control.do
  withLinearlyBO $ \l ->
    dup l & \(l, l') -> Control.do
      Control.pure $ borrow (Raw.fromListL kvs $ fromPB l) l'

insert :: (Keyed k) => k -> v -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE insert #-}
insert key val (UnsafeAlias dic) = case Raw.insert key val dic of
  !dic -> Control.pure (UnsafeAlias dic)

insertAll :: (Keyed k) => [(k, v)] -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE insertAll #-}
insertAll kvs (UnsafeAlias dic) = case Raw.insertAll kvs dic of
  !dic -> Control.pure (UnsafeAlias dic)

delete :: (Keyed k) => k -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE delete #-}
delete key (UnsafeAlias dic) = case Raw.delete key dic of
  !dic -> Control.pure (UnsafeAlias dic)

filter :: (Keyed k) => (v -> Bool) -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE filter #-}
filter p (UnsafeAlias dic) = case Raw.filter p dic of
  !dic -> Control.pure (UnsafeAlias dic)

filterWithKey :: (Keyed k) => (k -> v -> Bool) -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE filterWithKey #-}
filterWithKey p (UnsafeAlias dic) = case Raw.filterWithKey p dic of
  !dic -> Control.pure (UnsafeAlias dic)

mapMaybe :: (Keyed k) => (v -> Maybe v') -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v'))
{-# INLINE mapMaybe #-}
mapMaybe f (UnsafeAlias dic) = case Raw.mapMaybe f dic of
  !dic -> Control.pure (UnsafeAlias dic)

mapMaybeWithKey :: (Keyed k) => (k -> v -> Maybe v') -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v'))
{-# INLINE mapMaybeWithKey #-}
mapMaybeWithKey f (UnsafeAlias dic) = case Raw.mapMaybeWithKey f dic of
  !dic -> Control.pure (UnsafeAlias dic)

shrinkToFit :: (Keyed k) => Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE shrinkToFit #-}
shrinkToFit (UnsafeAlias dic) = case Raw.shrinkToFit dic of
  !dic -> Control.pure (UnsafeAlias dic)

alter :: (Keyed k) => (Maybe v -> Maybe v) -> k -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE alter #-}
alter f key (UnsafeAlias dic) = case Raw.alter f key dic of
  !dic -> Control.pure (UnsafeAlias dic)

alterF :: (Keyed k) => (Maybe v -> BO α (Ur (Maybe v))) -> k -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE alterF #-}
alterF f key (UnsafeAlias dic) = UnsafeAlias Control.<$> Raw.alterF f key dic

size :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE size #-}
size = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.size dic of
  (!sz, !_) -> Control.pure sz

capacity :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE capacity #-}
capacity = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.capacity dic of
  (!sz, !_) -> Control.pure sz

lookup :: (Keyed k) => k -> Borrow bk α (HashMap k v) %1 -> BO α (Ur (Maybe v))
{-# INLINE lookup #-}
lookup key = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.lookup key dic of
  (!mv, !_) -> Control.pure mv

member :: (Keyed k) => k -> Borrow bk α (HashMap k v) %1 -> BO α (Ur Bool)
{-# INLINE member #-}
member key = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.member key dic of
  (!b, !_) -> Control.pure b

toList :: Lend α (HashMap k v) %1 -> End α -> Ur [(k, v)]
{-# INLINE toList #-}
toList lend end = Raw.toList (reclaim lend end)
