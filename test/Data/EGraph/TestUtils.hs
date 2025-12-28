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
import Control.Monad qualified as P
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.EGraph.Types
import Data.Hashable.Lifted
import GHC.Base qualified as GHC
import Prelude.Linear

withNewEGraph ::
  (Hashable1 l) =>
  (forall α. Mut α (EGraph l) %1 -> BO α (Ur a)) %1 ->
  Linearly %1 ->
  Ur a
{-# NOINLINE withNewEGraph #-}
withNewEGraph = GHC.noinline \f lin -> DataFlow.do
  (v, graph) <- modifyLinearOnlyBO (new lin) f
  graph `lseq` v
