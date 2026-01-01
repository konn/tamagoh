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
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils
import Data.EGraph.EMatch.Relational
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Functor.Linear qualified as Data
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust)
import GHC.Generics qualified as GHC
import Prelude.Linear
import Prelude qualified as P

data Lang1 a = F !a !a | G !a | I !Int
  deriving
    ( P.Eq
    , P.Ord
    , P.Show
    , P.Functor
    , P.Foldable
    , P.Traversable
    )

deriveLanguage ''Lang1

intT :: Int -> Term Lang1
intT i = wrapTerm $ I i

mkCase1 :: Int -> Mut α (EGraph Lang1) %1 -> BO α (Ur [(EClassId, Substitution String)])
mkCase1 n egraph = Control.do
  (ns, egraph) <- forRebor egraph (NE.fromList [1 .. n]) \egraph i ->
    move i & \(Ur i) -> Control.do
      (Ur _, eid, egraph) <- addTerm egraph $ intT i
      Control.pure $ egraph `lseq` eid
  Ur ns <- Control.pure $ move ns
  (gs, egraph) <- forRebor egraph ns \egraph (Ur eid) -> Control.do
    (Ur geid, egraph) <- addNode egraph $ ENode $ G eid
    Control.pure $ egraph `lseq` Ur (fromJust geid)
  Ur gs <- Control.pure $ move gs
  (Ur _, egraph) <- merges (unur Data.<$> gs) egraph
  let fs = NE.zipWith (\(Ur nid) (Ur gid) -> ENode $ F nid gid) ns gs
  (fs, egraph) <- forRebor egraph fs \egraph node ->
    move node & \(Ur node) -> Control.do
      (Ur feid, egraph) <- addNode egraph node
      Control.pure $ egraph `lseq` fromJust feid
  Ur fs <- Control.pure $ move fs
  (Ur _, egraph) <- merges fs egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph \egraph ->
    ematch (PNode $ F (Metavar "a") $ PNode $ G (Metavar "a")) egraph
