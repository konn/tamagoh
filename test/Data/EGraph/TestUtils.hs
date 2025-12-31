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
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.TestUtils where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.EGraph.Types
import Data.Functor.Classes (Show1)
import Data.Hashable.Lifted
import Data.Unrestricted.Linear.Lifted (Copyable1)
import Debug.Trace.Linear qualified as DT
import Prelude.Linear
import Text.Show.Borrowed (display)

withNewEGraph ::
  (Hashable1 l, Copyable1 l, Show1 l) =>
  (forall α. Mut α (EGraph l) %1 -> BO α (Ur a)) %1 ->
  Ur a
withNewEGraph f =
  linearly \lin -> DataFlow.do
    (v, graph) <- modifyLinearOnlyBO (new lin) \eg -> Control.do
      (Ur shown, eg) <- sharing eg $ \eg -> display eg
      () <- DT.trace ("Creating new EGraph: ") $ Control.pure ()
      () <- DT.trace ("    " <> shown) $ Control.pure ()
      f eg
    graph `lseq` v
