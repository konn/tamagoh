{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

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
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (HashMap, Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.HashSet qualified as IHS
import Data.Linear.Witness.Compat (fromPB)
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

empty :: (Keyed k) => Int -> BO α (Mut α (HashMap k v), Lend α (HashMap k v))
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    dup l & \(l, l') -> Control.do
      Control.pure $ borrow (Raw.emptyL size $ fromPB l) l'

-- TODO: more efficient implementation
insert :: (Keyed k) => k -> v %1 -> Mut α (HashMap k v) %1 -> BO α (Maybe v, Mut α (HashMap k v))
{-# NOINLINE insert #-}
insert key = Unsafe.toLinear2 \v dic -> Control.do
  (mold, dic) <- delete key dic
  !dic <- case dic of
    UnsafeAlias !dic ->
      Control.pure $! Raw.insert key v dic
  Control.pure (mold, UnsafeAlias dic)

-- TODO: more efficient implementation
delete :: (Keyed k) => k -> Mut α (HashMap k v) %1 -> BO α (Maybe v, Mut α (HashMap k v))
{-# NOINLINE delete #-}
delete key (UnsafeAlias dic) = case Raw.lookup key dic of
  (!(Ur !(Just !v)), !dic) -> case Raw.delete key dic of
    !dic -> Control.pure (Just v, UnsafeAlias dic)
  (!(Ur Nothing), !dic) -> Control.pure (Nothing, UnsafeAlias dic)

shrinkToFit :: (Keyed k) => Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE shrinkToFit #-}
shrinkToFit (UnsafeAlias dic) = case Raw.shrinkToFit dic of
  !dic -> Control.pure (UnsafeAlias dic)

alter :: (Keyed k) => (Maybe v %1 -> Maybe v) %1 -> k -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE alter #-}
alter = Unsafe.toLinear \f -> \key (UnsafeAlias dic) -> case Raw.alter (Unsafe.toLinear f) key dic of
  !dic -> Control.pure (UnsafeAlias dic)

alterF :: (Keyed k) => (Maybe v %1 -> BO α (Maybe v)) -> k -> Mut α (HashMap k v) %1 -> BO α (Mut α (HashMap k v))
{-# INLINE alterF #-}
alterF f key (UnsafeAlias dic) = UnsafeAlias Control.<$> Raw.alterF (\x -> Unsafe.toLinear Ur Control.<$> f x) key dic

size :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE size #-}
size = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.size dic of
  (!sz, !_) -> Control.pure sz

capacity :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
{-# INLINE capacity #-}
capacity = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.capacity dic of
  (!sz, !_) -> Control.pure sz

lookup ::
  (Keyed k) =>
  k ->
  Borrow bk α (HashMap k v) %1 ->
  BO α (Maybe (Borrow bk α v))
{-# INLINE lookup #-}
lookup key = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.lookup key dic of
  (!(Ur mv), !_) -> Control.pure (UnsafeAlias Data.<$> mv)

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
member key = Unsafe.toLinear \(UnsafeAlias dic) -> case Raw.member key dic of
  (!b, !_) -> Control.pure b

toList :: Lend α (HashMap k v) %1 -> End α -> [(k, v)]
{-# INLINE toList #-}
toList lend end = unur $ Raw.toList (reclaim lend end)
