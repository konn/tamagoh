{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Set.Mutable.Linear.Borrowed (
  Set,
  empty,
  singleton,
  fromList,
  insert,
  inserts,
  toList,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Linear.Witness.Compat (fromPB)
import Data.Set.Mutable.Linear (Keyed)
import Data.Set.Mutable.Linear.Witness qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe

newtype Set k = Set (Raw.Set k)
  deriving newtype (Consumable, Dupable)

empty :: (Keyed k) => Int -> BO α (Set k)
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    Control.pure $ Set $ Raw.emptyL size $ fromPB l

singleton :: (Keyed k) => k %1 -> BO α (Set k)
{-# INLINE singleton #-}
singleton = Unsafe.toLinear \key -> withLinearlyBO \l ->
  Control.pure $ Set $ Raw.fromListL [key] $ fromPB l

fromList :: (Keyed k) => [k] %1 -> BO α (Set k)
{-# INLINE fromList #-}
fromList = Unsafe.toLinear \keys -> withLinearlyBO \l ->
  Control.pure $ Set $ Raw.fromListL keys $ fromPB l

insert :: (Keyed k) => k %1 -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
{-# INLINE insert #-}
insert = Unsafe.toLinear2 \key (UnsafeAlias (Set set)) -> Control.do
  case Raw.insert key set of
    !set -> Control.pure (UnsafeAlias (Set set))

inserts :: (Keyed k) => [k] %1 -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
{-# INLINE inserts #-}
inserts [] old = Control.pure old
inserts (k : ks) old = Control.do
  old <- insert k old
  inserts ks old

toList :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α [k]
{-# NOINLINE toList #-}
toList (UnsafeAlias (Set set)) = case Raw.toList set of
  !(Ur !lst) -> Control.pure lst
