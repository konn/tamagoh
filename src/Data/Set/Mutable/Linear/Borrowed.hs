{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Set.Mutable.Linear.Borrowed (Set, empty, singleton) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Linear.Witness.Compat (fromPB)
import Data.Set.Mutable.Linear (Keyed, Set)
import Data.Set.Mutable.Linear.Witness qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe)
import Unsafe.Linear qualified as Unsafe

empty :: (Keyed k) => Int -> BO α (Mut α (Set k), Lend α (Set k))
{-# INLINE empty #-}
empty size = Control.do
  withLinearlyBO $ \l ->
    dup l & \(l, l') -> Control.do
      Control.pure $ borrow (Raw.emptyL size $ fromPB l) l'

singleton :: (Keyed k) => k %1 -> BO α (Set k)
{-# INLINE singleton #-}
singleton = Unsafe.toLinear \key -> withLinearlyBO \l ->
  Control.pure (Raw.fromListL [key] (fromPB l))
