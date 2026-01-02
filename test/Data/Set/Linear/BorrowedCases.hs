{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.Set.Linear.BorrowedCases (
  module Data.Set.Linear.BorrowedCases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Coerce.Directed (upcast)
import Data.Hashable (Hashable)
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import GHC.Generics (Generic)
import Generics.Linear (Generically (..))
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear

withNewSet ::
  (Hashable k) =>
  (forall α. Mut α (Set k) %1 -> BO α (Ur a)) %1 ->
  Ur a
withNewSet = \f ->
  linearly \lin -> DataFlow.do
    (v, graph) <- modifyLinearOnlyBO (Set.empty 16 lin) f
    graph `lseq` v

data SetCaseResult = SetCaseResult
  { finalEnts :: ![(Int)]
  , finalAnswer :: !Bool
  }
  deriving (Show)

case1 :: Mut α (Set Int) %1 -> BO α (Ur SetCaseResult)
case1 dic = Control.do
  dic <- Set.insert 1 dic
  (Ur finalAnswer, dic) <- sharing dic \dic -> Set.member 1 dic
  Ur finalEnts <- move Control.<$> Set.toList dic
  Control.pure $
    move finalAnswer
      & \(Ur finalAnswer) ->
        Ur SetCaseResult {..}

case2 :: Mut α (Set Int) %1 -> BO α (Ur SetCaseResult)
case2 dic = Control.do
  dic <- Set.insert 2 dic
  (Ur finalAnswer, dic) <- sharing dic \dic -> Set.member 2 dic
  Ur finalEnts <- move Control.<$> Set.toList dic
  Control.pure $
    move finalAnswer
      & \(Ur finalAnswer) -> Ur SetCaseResult {..}

data SetDupResult = SetDupResult
  { initOrig :: ![Int]
  , insertedOrig :: ![Int]
  , initDup :: ![Int]
  , twiceInsertedOrig :: ![Int]
  , finalDup :: ![Int]
  }
  deriving (Show, Generic)

deriveGeneric ''SetDupResult

deriving via Generically SetDupResult instance Consumable SetDupResult

deriving via Generically SetDupResult instance Dupable SetDupResult

deriving via Generically SetDupResult instance Movable SetDupResult

copyCase :: Mut α (Set Int) %1 -> BO α (Ur SetDupResult)
copyCase dic = Control.do
  (result, dic) <- reborrowing' dic \dic -> Control.do
    (initOrig, dic) <- sharing dic $ \dic -> Set.toList dic
    dic <- Set.insert 1 dic
    (insertedOrig, dic) <- sharing dic $ \dic -> Set.toList dic
    (dupedRaw, dic) <- sharing dic $ \dic -> Control.pure $ copy dic
    let %1 !(duped, lentDuped) = borrowLinearOnly dupedRaw
    (initDup, duped) <- sharing duped \duped -> Set.toList duped
    dic <- Set.insert 2 dic
    (twiceInsertedOrig, dic) <- sharing dic $ \dic -> Set.toList dic
    (finalDup, duped) <- sharing duped \duped -> Set.toList duped

    Control.pure $ \end ->
      reclaim lentDuped (upcast end)
        `lseq` duped
        `lseq` dic
        `lseq` SetDupResult {..}
  Control.pure $ dic `lseq` move result