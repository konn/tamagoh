{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.Mutable.Linear.Borrowed.Internal (
  module Data.HashMap.Mutable.Linear.Borrowed.Internal,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (coerceLin, deepCloneArray')
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Internal qualified as Raw
import Data.List.Linear qualified as List
import Data.Maybe qualified as P
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Unrestricted.Linear qualified as Ur
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Text.Show.Borrowed (Display (..))
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

deepCloneHashMap :: (Dupable v) => Raw.HashMap k v %1 -> (Raw.HashMap k v, Raw.HashMap k v)
deepCloneHashMap (Raw.HashMap !i !j !robinArr) = DataFlow.do
  (robinArr, !robinArr2) <- deepCloneArray' dupRobinVal robinArr
  (Raw.HashMap i j robinArr, Raw.HashMap i j robinArr2)

dupRobinVal ::
  (Dupable v) =>
  Maybe (Raw.RobinVal k v) %1 ->
  (Maybe (Raw.RobinVal k v), Maybe (Raw.RobinVal k v))
dupRobinVal = Unsafe.toLinear \case
  Nothing -> (Nothing, Nothing)
  Just (Raw.RobinVal (Raw.PSL i) !k !v) -> DataFlow.do
    !i' <- Unsafe.toLinear (\(_, !x) -> x) $ dup i
    !v' <- Unsafe.toLinear (\(_, !x) -> x) $ dup v
    (Just (Raw.RobinVal (Raw.PSL i) k v), Just (Raw.RobinVal (Raw.PSL i') k v'))

-- NOTE: we need indirection here, because 'Raw.HashMap' uses Array behind the scenes,
-- and regrows new array. If the our 'HashMap' is stored in another mutable borrows,
-- then just threading through 'Raw.HashMap' would discard the change to the outer borrow.
newtype HashMap k v = HM (Ref (Raw.HashMap k v))
  deriving newtype (LinearOnly)

instance Consumable (HashMap k v) where
  -- FIXME: stop leaking
  consume = \(HM ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

instance (Show k, Display v) => Display (HashMap k v) where
  displayPrec _ bor = Control.do
    lst <- toBorrowList bor
    Ur lst <-
      foldr (Ur.lift2 (P..)) (Ur id)
        . List.intersperse (Ur $ showString ", ")
        Control.<$> Data.mapM
          ( \(Ur !k, v) ->
              share v & \(Ur v) -> Control.do
                Ur sv <- displayPrec 0 v
                Control.pure $ Ur $ showChar '(' P.. showsPrec 0 k P.. showString ", " P.. sv P.. showChar ')'
          )
          lst
    Control.pure $ Ur $ showString "{" P.. lst P.. showString "}"

instance (Dupable v) => Dupable (HashMap k v) where
  -- NOTE: we need to duplicate underlying array deeply, to dup the inner mutable arrays properly.
  -- otherwise, the duplicated cells would be 'consume'd earlier and can (and actually) cause SEGV.
  dup2 = Unsafe.toLinear \(HM !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !hm) <- Unsafe.toLinear (\ref -> (ref, freeRef ref)) ref
    hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ deepCloneHashMap hm
    (HM ref, HM $ Ref.new hm' lin)

toBorrowList ::
  Borrow bk α (HashMap k v) %1 ->
  BO α [(Ur k, (Borrow bk α v))]
toBorrowList ref =
  share ref & \(Ur dic) -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    Unsafe.toLinear
      ( \(Raw.HashMap _ _ !robinArr) ->
          Array.toList robinArr
            & \(Ur elems) ->
              Control.pure
                $! P.map (\(Raw.RobinVal _ !k !v) -> (Ur k, UnsafeAlias v))
                $! P.catMaybes elems
      )
      dic

coerceBor ::
  forall k v bk α.
  Borrow bk α (HashMap k v) %1 ->
  Borrow bk α (Ref (Raw.HashMap k v))
{-# INLINE coerceBor #-}
coerceBor = coerceLin

recoerceBor ::
  forall k v bk α.
  Borrow bk α (Ref (Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMap k v)
{-# INLINE recoerceBor #-}
recoerceBor = coerceLin
