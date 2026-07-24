{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{- | Internals of the borrowable dense-id slot table. The unsafe
alias\/ownership machinery here is a verbatim port of
"Data.HashMap.Mutable.Linear.Borrowed.Internal" — see the NOTEs there;
nothing novel is introduced.
-}
module Data.SlotMap.Mutable.Linear.Borrowed.Internal (
  module Data.SlotMap.Mutable.Linear.Borrowed.Internal,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe
import Control.Monad.Borrow.Pure.Utils (coerceLin, deepCloneArray', unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Array.Mutable.Linear.Witness qualified as ArrayW
import Data.DList (DList)
import Data.DList qualified as DL
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.Linear.Witness.Compat (fromPB)
import Data.List.Linear qualified as List
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow (Ref)
import Data.Ref.Linear.Borrow qualified as Ref
import Data.Unrestricted.Linear qualified as Ur
import Prelude.Linear hiding (insert, lookup)
import Text.Show.Borrowed (Display (..))
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

{- | Growable slot table addressed by dense 'Int' ids (egglog-style class
storage: no hashing, no probing — a slot per id). Slots hold
@Nothing@ for never-used indices and deleted holes; ids are expected to be
allocated densely and never reused, so holes need no compaction and
capacity is proportional to the largest id ever inserted.

Fields: live count (number of @Just@ slots), bound (one past the highest
index ever written; the iteration limit), capacity, slots.

NOTE [Ref indirection]: growth reallocates the backing array; without the
'Ref' in 'SlotMap', a regrow inside an outer mutable borrow would be lost —
same note as "Data.HashMap.Mutable.Linear.Borrowed.Internal".
-}
data RawSlotMap v where
  RawSlotMap ::
    !Int ->
    !Int ->
    !Int ->
    !(Array.Array (Maybe v)) %1 ->
    RawSlotMap v

newtype SlotMap v = SM (Ref (RawSlotMap v))
  deriving newtype (LinearOnly)

instance Consumable (RawSlotMap v) where
  consume (RawSlotMap live bound cap arr) =
    live `lseq` bound `lseq` cap `lseq` consume arr

instance Consumable (SlotMap v) where
  consume = \(SM ref) -> consume $ Ref.free ref
  {-# INLINE consume #-}

coerceBor ::
  forall v bk α.
  Borrow bk α (SlotMap v) %1 ->
  Borrow bk α (Ref (RawSlotMap v))
{-# INLINE coerceBor #-}
coerceBor = coerceLin

recoerceBor ::
  forall v bk α.
  Borrow bk α (Ref (RawSlotMap v)) %1 ->
  Borrow bk α (SlotMap v)
{-# INLINE recoerceBor #-}
recoerceBor = coerceLin

rawEmptyL :: Int -> Linearly %1 -> RawSlotMap v
rawEmptyL cap0 lin =
  let !cap = P.max 1 cap0
   in RawSlotMap 0 0 cap (ArrayW.allocL cap Nothing (fromPB lin))

{- | Aliasing read: the 'Ur' payload aliases the stored value; callers must
rewrap it with 'UnsafeAlias' (borrow manufacture) or drop it.
-}
rawLookup :: Int -> RawSlotMap v %1 -> (Ur (Maybe v), RawSlotMap v)
rawLookup !i (RawSlotMap live bound cap arr)
  | i P.< 0 P.|| i P.>= bound = (Ur Nothing, RawSlotMap live bound cap arr)
  | otherwise =
      Array.unsafeGet i arr & \(Ur mv, arr) ->
        (Ur mv, RawSlotMap live bound cap arr)

rawMember :: Int -> RawSlotMap v %1 -> (Ur Bool, RawSlotMap v)
rawMember !i sm =
  rawLookup i sm & \(Ur mv, sm) -> (Ur (P.maybe False (\_ -> True) mv), sm)

rawSize :: RawSlotMap v %1 -> (Ur Int, RawSlotMap v)
rawSize (RawSlotMap live bound cap arr) = (Ur live, RawSlotMap live bound cap arr)

{- | Write slot @i@ (growing by doubling, cf. @Data.UnionFind.Linear.fresh@),
returning the old content OWNED. Ownership argument: the slot pointer is
overwritten before the old value is returned, so the returned reference is
unique — the same transfer the hashmap's alterF-based delete performs.
-}
rawInsert :: Int -> v %1 -> RawSlotMap v %1 -> (Maybe v, RawSlotMap v)
rawInsert !i = Unsafe.toLinear2 \ !v (RawSlotMap live bound cap arr) ->
  let growTo !c = if i P.< c then c else growTo (c P.* 2)
      (!cap', !arr')
        | i P.< cap = (cap, arr)
        | otherwise =
            let !c' = growTo (P.max 16 (cap P.* 2))
             in (c', Array.resize c' Nothing arr)
   in Array.unsafeGet i arr' & \(Ur !old, arr'') ->
        Array.unsafeSet i (Just v) arr'' & \arr3 ->
          let !live' = case old of Nothing -> live P.+ 1; Just _ -> live
              !bound' = P.max bound (i P.+ 1)
           in (old, RawSlotMap live' bound' cap' arr3)

-- | Clear slot @i@, returning the old content OWNED (see 'rawInsert').
rawDelete :: Int -> RawSlotMap v %1 -> (Maybe v, RawSlotMap v)
rawDelete !i = Unsafe.toLinear \(RawSlotMap live bound cap arr) ->
  if i P.< 0 P.|| i P.>= bound
    then (Nothing, RawSlotMap live bound cap arr)
    else
      Array.unsafeGet i arr & \(Ur !old, arr') ->
        case old of
          Nothing -> (Nothing, RawSlotMap live bound cap arr')
          Just _ ->
            Array.unsafeSet i Nothing arr' & \arr'' ->
              (old, RawSlotMap (live P.- 1) bound cap arr'')

-- | Interior borrows of every live slot, ascending index order.
toBorrowList ::
  forall bk α v m.
  Borrow bk α (SlotMap v) %m ->
  BO α [(Ur Int, Borrow bk α v)]
toBorrowList ref =
  share ref & \(Ur sm) -> Control.do
    Ur (UnsafeAlias !raw) <- Ref.readShare (coerceBor sm)
    Unsafe.toLinear
      ( \(RawSlotMap _ bound _ !arr0) ->
          let go :: Int -> Array.Array (Maybe v) %1 -> DList (Ur Int, Borrow bk α v) -> BO α [(Ur Int, Borrow bk α v)]
              go !i !arr !acc
                | i P.< bound =
                    Array.unsafeGet i arr & \case
                      (Ur (Just !v), !arr) ->
                        go (i P.+ 1) arr (DL.snoc acc (Ur i, UnsafeAlias v))
                      (Ur Nothing, !arr) -> go (i P.+ 1) arr acc
                | otherwise = unsafeLeak arr `lseq` Control.pure (DL.toList acc)
           in go 0 arr0 P.mempty
      )
      raw

deepCloneRawSlotMap :: (Dupable v) => RawSlotMap v %1 -> (RawSlotMap v, RawSlotMap v)
deepCloneRawSlotMap (RawSlotMap !live !bound !cap !arr) = DataFlow.do
  (arr, !arr2) <- deepCloneArray' dupSlot arr
  (RawSlotMap live bound cap arr, RawSlotMap live bound cap arr2)

dupSlot :: (Dupable v) => Maybe v %1 -> (Maybe v, Maybe v)
dupSlot = Unsafe.toLinear \case
  Nothing -> (Nothing, Nothing)
  Just !v -> DataFlow.do
    !v' <- Unsafe.toLinear (\(_, !x) -> x) $ dup v
    (Just v, Just v')

instance (Dupable v) => Dupable (SlotMap v) where
  -- NOTE: duplicate the underlying array deeply, to dup the inner mutable
  -- values properly — otherwise the duplicated cells would be 'consume'd
  -- earlier and can cause SEGV (same note as the borrowed hashmap).
  dup2 = Unsafe.toLinear \(SM !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !sm) <- Unsafe.toLinear (\ref -> (ref, Ref.free ref)) ref
    sm' <- Unsafe.toLinear (\(!_, !sm') -> sm') $ deepCloneRawSlotMap sm
    (SM ref, SM $ Ref.new sm' lin)

instance (Display v) => Display (SlotMap v) where
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
