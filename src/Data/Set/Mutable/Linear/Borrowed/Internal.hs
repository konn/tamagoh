{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.Set.Mutable.Linear.Borrowed.Internal (
  module Data.Set.Mutable.Linear.Borrowed.Internal,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (coerceLin)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed.Internal (deepCloneHashMap)
import Data.HashMap.Mutable.Linear.Internal qualified as RawHM
import Data.List.Linear qualified as List
import Data.Maybe qualified as P
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Set.Mutable.Linear.Internal qualified as Raw
import Data.Unrestricted.Linear qualified as Ur
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, null, take)
import Text.Show.Borrowed
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- NOTE: we need indirection here, because 'Raw.Set' uses Array behind the scenes,
-- and regrows new array. If the our 'Set' is stored in another mutable borrows,
-- then just threading through 'Raw.Set' would discard the change to the outer borrow.
newtype Set k = Set (Ref (Raw.Set k))
  deriving newtype (LinearOnly)

instance Consumable (Set k) where
  consume = \(Set ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

instance Dupable (Set k) where
  -- NOTE: we need to duplicate underlying array deeply, to dup the inner mutable arrays properly.
  -- otherwise, the duplicated cells would be 'consume'd earlier and can (and actually) cause SEGV.
  dup2 = Unsafe.toLinear \(Set !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !hm) <- Unsafe.toLinear (\ref -> (ref, freeRef ref)) ref
    case hm of
      Raw.Set hm -> DataFlow.do
        !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ deepCloneHashMap hm
        (Set ref, Set $! Ref.new (Raw.Set hm') lin)

instance Copyable (Set k) where
  -- NOTE: we need to duplicate underlying array deeply, to dup the inner mutable arrays properly.
  -- otherwise, the duplicated cells would be 'consume'd earlier and can (and actually) cause SEGV.
  copy = Unsafe.toLinear \(UnsafeAlias (Set !ref)) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    !hm <- freeRef ref
    case hm of
      Raw.Set hm -> DataFlow.do
        !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ deepCloneHashMap hm
        Set $! Ref.new (Raw.Set hm') lin

instance (Display k) => Display (Set k) where
  displayPrec _ bor = Control.do
    lst <- toBorrowList bor
    Ur lst <-
      foldr (Ur.lift2 (P..)) (Ur id)
        . List.intersperse (Ur $ showString ", ")
        Control.<$> Data.mapM (\x -> move x & \(Ur x) -> displayPrec 0 x) lst
    Control.pure $ Ur $ showString "{" P.. lst P.. showString "}"

toBorrowList :: Borrow bk α (Set k) %m -> BO α [Borrow bk α k]
toBorrowList =
  askRaw_
    ( \(Raw.Set (RawHM.HashMap _ _ robinArr)) ->
        Array.toList robinArr
          & \(Ur elems) ->
            elems
              P.& P.catMaybes
              P.& P.map (\(RawHM.RobinVal _ !k ()) -> UnsafeAlias k)
    )

askRaw_ ::
  (Raw.Set k %1 -> a) %1 ->
  Borrow bk α (Set k) %m ->
  BO α a
askRaw_ f dic = case share dic of
  Ur dic -> Control.do
    Ur (UnsafeAlias dic) <- readSharedRef (coerceBor dic)
    case f dic of
      !res -> Control.pure res

coerceBor ::
  forall k bk α.
  Borrow bk α (Set k) %1 ->
  Borrow bk α (Ref (Raw.Set k))
{-# INLINE coerceBor #-}
coerceBor = coerceLin

recoerceBor ::
  forall k bk α.
  Borrow bk α (Ref (Raw.Set k)) %1 ->
  Borrow bk α (Set k)
{-# INLINE recoerceBor #-}
recoerceBor = coerceLin
