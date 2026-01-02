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

module Data.HashMap.Linear.BorrowedCases (
  module Data.HashMap.Linear.BorrowedCases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable (Hashable)
import Prelude.Linear

withNewHashMap ::
  (Hashable k) =>
  (forall α. Mut α (HashMap k v) %1 -> BO α (Ur a)) %1 ->
  Ur a
withNewHashMap f =
  linearly \lin -> DataFlow.do
    (v, graph) <- modifyLinearOnlyBO (HMB.empty 16 lin) f
    graph `lseq` v

data HMCaseResult = HMCaseResult
  { residence :: !(Maybe Int)
  , finalEnts :: ![(Int, Int)]
  , finalAnswer :: !(Maybe Int)
  }
  deriving (Show)

case1 :: Mut α (HashMap Int Int) %1 -> BO α (Ur HMCaseResult)
case1 dic = Control.do
  (residence, dic) <- HMB.insert 1 1 dic
  (finalAnswer, dic) <- sharing dic \dic -> Data.fmap copy Control.<$> HMB.lookup 1 dic
  Ur finalEnts <- HMB.toList dic
  Control.pure $
    move (residence, finalAnswer)
      & \(Ur (residence, finalAnswer)) ->
        Ur HMCaseResult {..}

case2 :: Mut α (HashMap Int Int) %1 -> BO α (Ur HMCaseResult)
case2 dic = Control.do
  (residence, dic) <- HMB.insert 2 2 dic
  (finalAnswer, dic) <- sharing dic \dic -> Data.fmap copy Control.<$> HMB.lookup 2 dic
  Ur finalEnts <- HMB.toList dic
  Control.pure $
    move (residence, finalAnswer)
      & \(Ur (residence, finalAnswer)) ->
        Ur HMCaseResult {..}
