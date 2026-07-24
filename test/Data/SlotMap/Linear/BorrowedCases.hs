{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.SlotMap.Linear.BorrowedCases (
  module Data.SlotMap.Linear.BorrowedCases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Functor.Linear qualified as Data
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as RefB
import Data.SlotMap.Mutable.Linear.Borrowed (SlotMap)
import Data.SlotMap.Mutable.Linear.Borrowed qualified as SM
import Prelude.Linear
import Prelude qualified as P

-- All cases start at capacity 1 so growth paths are always exercised.
withNewSlotMap ::
  (forall α. Mut α (SlotMap v) %1 -> BO α (Ur a)) %1 ->
  Ur a
withNewSlotMap f =
  linearly \lin -> DataFlow.do
    (v, sm) <- modifyLinearOnlyBO (SM.empty 1 lin) f
    sm `lseq` v

data DenseResult = DenseResult
  { allFresh :: !Bool
  , liveCount :: !Int
  , entries :: ![(Int, Int)]
  }
  deriving (P.Show, P.Eq)

-- | Dense push 0..99 through several regrows; ascending iteration order.
caseDense :: forall α. Mut α (SlotMap Int) %1 -> BO α (Ur DenseResult)
caseDense sm = Control.do
  (Ur allFresh, sm) <- go 0 True sm
  (Ur liveCount, sm) <- sharing sm SM.size
  Ur entries <- collectEntries sm
  Control.pure $ Ur DenseResult {..}
  where
    go :: Int -> Bool -> Mut α (SlotMap Int) %1 -> BO α (Ur Bool, Mut α (SlotMap Int))
    go !i !fresh sm
      | i P.>= 100 = Control.pure (Ur fresh, sm)
      | otherwise = Control.do
          (mold, sm) <- SM.insert i (i P.* 10) sm
          move mold & \(Ur mold) ->
            go (i P.+ 1) (fresh P.&& P.maybe True (\_ -> False) mold) sm

collectEntries :: Mut α (SlotMap Int) %1 -> BO α (Ur [(Int, Int)])
collectEntries sm = Control.do
  (Ur rows, sm) <- sharing sm \sm -> Control.do
    ents <- SM.toBorrowList sm
    move
      Control.<$> Data.mapM
        (\(Ur k, v) -> move (copy v) & \(Ur val) -> Control.pure (Ur (k, val)))
        ents
  Control.pure $ sm `lseq` Ur (P.map (\(Ur r) -> r) rows)

data HolesResult = HolesResult
  { afterDeletes :: !Int
  , evenGone :: !Bool
  , oddKept :: !Bool
  , doubleDelete :: !(Maybe Int)
  , refillFresh :: !(Maybe Int)
  , finalCount :: !Int
  }
  deriving (P.Show, P.Eq)

-- | Deletion holes, double-delete, and hole re-insert keep the live count right.
caseHoles :: forall α. Mut α (SlotMap Int) %1 -> BO α (Ur HolesResult)
caseHoles sm = Control.do
  sm <- fill 0 sm
  sm <- dels 0 sm
  (Ur afterDeletes, sm) <- sharing sm SM.size
  (Ur evenGone, sm) <- sharing sm (SM.member 4)
  (Ur oddKept, sm) <- sharing sm (SM.member 5)
  (doubleDelete, sm) <- SM.delete 4 sm
  (refillFresh, sm) <- SM.insert 4 (444 :: Int) sm
  (Ur finalCount, sm) <- sharing sm SM.size
  Control.pure $
    move (doubleDelete, refillFresh) & \(Ur (doubleDelete, refillFresh)) ->
      sm `lseq` Ur HolesResult {evenGone = P.not evenGone, ..}
  where
    fill :: Int -> Mut α (SlotMap Int) %1 -> BO α (Mut α (SlotMap Int))
    fill !i sm
      | i P.>= 10 = Control.pure sm
      | otherwise = Control.do
          (mold, sm) <- SM.insert i i sm
          mold `lseq` fill (i P.+ 1) sm
    dels :: Int -> Mut α (SlotMap Int) %1 -> BO α (Mut α (SlotMap Int))
    dels !i sm
      | i P.>= 10 = Control.pure sm
      | otherwise = Control.do
          (mold, sm) <- SM.delete i sm
          mold `lseq` dels (i P.+ 2) sm

{- | Linear values: delete hands back the OWNED Ref; mutation through a
lookup borrow persists across several regrows (interior borrows alias the
boxed value, not the array slot).
-}
caseOwnedAndGrowth :: forall α. Mut α (SlotMap (Ref.Ref Int)) %1 -> BO α (Ur (Int, Int))
caseOwnedAndGrowth sm = Control.do
  ref0 <- asksLinearly (Ref.new (0 :: Int))
  (m0, sm) <- SM.insert 0 ref0 sm
  -- mutate slot 0 through an interior borrow
  sm <- reborrowing_ sm \sm -> Control.do
    mref <- SM.lookup 0 sm
    case mref of
      Nothing -> Control.pure ()
      Just ref -> Control.do
        (Ur (), ref) <- RefB.update (\v -> v `lseq` Control.pure (Ur (), 42 :: Int)) ref
        Control.pure (consume ref)
  -- force several regrows past the initial capacity
  sm <- fill 1 sm
  -- the mutation must still be visible; delete returns the owned Ref
  (mref, sm) <- SM.delete 0 sm
  (Ur sz, sm) <- sharing sm SM.size
  case mref of
    Nothing -> Control.pure $ m0 `lseq` sm `lseq` Ur (-1, sz)
    Just ref ->
      move (Ref.free ref) & \(Ur v) ->
        Control.pure $ m0 `lseq` sm `lseq` Ur (v, sz)
  where
    fill :: Int -> Mut α (SlotMap (Ref.Ref Int)) %1 -> BO α (Mut α (SlotMap (Ref.Ref Int)))
    fill !i sm
      | i P.>= 64 = Control.pure sm
      | otherwise = Control.do
          ref <- asksLinearly (Ref.new i)
          (mold, sm) <- SM.insert i ref sm
          mold `lseq` fill (i P.+ 1) sm

-- | Sparse insert far past the bound on an empty table.
caseSparse :: forall α. Mut α (SlotMap Int) %1 -> BO α (Ur (Bool, Int, [(Int, Int)]))
caseSparse sm = Control.do
  (mold, sm) <- SM.insert 10 (1010 :: Int) sm
  (Ur missing, sm) <- sharing sm (SM.member 3)
  (Ur sz, sm) <- sharing sm SM.size
  Ur entries <- collectEntries sm
  Control.pure $
    move mold & \(Ur mold) ->
      Ur (P.maybe True (\_ -> False) mold P.&& P.not missing, sz, entries)
