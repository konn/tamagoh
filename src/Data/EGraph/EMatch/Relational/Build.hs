{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.Relational.Build (buildDatabase) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Data.EGraph.EMatch.Relational.Types
import Data.EGraph.Types
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Maybe (fromJust)
import Data.Traversable (Traversable)
import Data.Unrestricted.Linear qualified as Ur
import Prelude.Linear

buildDatabase ::
  (HasDatabase l, Movable1 l, Traversable l) =>
  Borrow k α (EGraph l) %1 ->
  BO α (Ur (Database l))
buildDatabase egraph =
  share egraph & \(Ur egraph) -> Control.do
    Ur nodes <-
      HMB.toList (egraph .# hashconsL)
        Control.>>= Control.fmap move
        . Data.mapM \(enode, id) -> do
          (,)
            Control.<$> (unur . Ur.lift fromJust Control.<$> canonicalize egraph enode)
            Control.<*> (unur Control.<$> unsafeFind egraph id)
    Control.pure
      $ Ur
      $ fromRelations
      $ map (\(ENode args, id) -> MkRel {id, args}) nodes
