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

module Data.EGraph.EMatch.RelationalCases (
  module Data.EGraph.EMatch.RelationalCases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Control.Monad.Borrow.Pure.Utils
import Data.EGraph.EMatch.Relational
import Data.EGraph.EMatch.Relational.Database (HasDatabase)
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.Functor.Classes
import Data.Functor.Linear qualified as Data
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty qualified as NE
import Debug.Trace.Linear qualified as DT
import GHC.Generics (Generically1 (..))
import GHC.Generics qualified as GHC
import Generics.Linear.TH qualified as GLC
import Prelude.Linear
import Text.Show.Deriving (deriveShow1)
import Prelude qualified as P

data Lang1 a = F !a !a | G !a | I !Int
  deriving
    ( P.Eq
    , P.Ord
    , P.Show
    , P.Functor
    , P.Foldable
    , P.Traversable
    , GHC.Generic
    , GHC.Generic1
    )
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1, HasDatabase) via Generically1 Lang1

deriveShow1 ''Lang1

intT :: Int -> Term Lang1
intT i = wrapTerm $ I i

GLC.deriveGenericAnd1 ''Lang1

deriving via Generically1 Lang1 instance Movable1 Lang1

mkCase1 :: Int -> Mut α (EGraph Lang1) %1 -> BO α (Ur [Substitution String])
mkCase1 n egraph = Control.do
  (ns, egraph) <- forRebor egraph (NE.fromList [1 .. n]) \egraph i ->
    move i & \(Ur i) -> Control.do
      (Ur _, eid, egraph) <- fromTerm egraph $ intT i
      Control.pure $ egraph `lseq` eid
  Ur ns <- Control.pure $ move ns
  () <- DT.trace ("added nodes: " <> show (Data.fmap unur ns)) $ Control.pure ()
  (gs, egraph) <- forRebor egraph ns \egraph (Ur eid) -> Control.do
    () <- DT.trace ("Adding g(" <> show eid <> ")") $ Control.pure ()
    (Ur geid, egraph) <- addNode egraph $ ENode $ G eid
    () <- DT.trace ("Added g node: " <> show geid) $ Control.pure ()
    Control.pure $ egraph `lseq` Ur geid
  Ur gs <- Control.pure $ move gs
  () <- DT.trace ("added gs nodes: " <> show (Data.fmap unur gs)) $ Control.pure ()
  (Ur _, egraph) <- merges (unur Data.<$> gs) egraph
  let fs = NE.zipWith (\(Ur nid) (Ur gid) -> ENode $ F nid gid) ns gs
  (fs, egraph) <- forRebor egraph fs \egraph node ->
    move node & \(Ur node) -> Control.do
      (Ur feid, egraph) <- addNode egraph node
      Control.pure $ egraph `lseq` feid
  Ur fs <- Control.pure $ move fs
  (Ur _, egraph) <- merges fs egraph
  egraph <- rebuild egraph
  () <- DT.trace "rebuilt" $ Control.pure ()
  uncurry (flip lseq) Control.<$> sharing egraph \egraph ->
    ematch (PNode $ F (Metavar "a") $ PNode $ G (Metavar "a")) egraph
