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

module Data.EGraph.Types.EGraph.Internal (
  module Data.EGraph.Types.EGraph.Internal,
) where

import Algebra.Semilattice (Semilattice)
import Control.Functor.Linear qualified as Control
import Control.Lens (Lens', view, _1, _2, _3, _4)
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Data.Bifunctor qualified as Bi
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses.Internal (EClasses)
import Data.EGraph.Types.ENode
import Data.Functor.Classes (Show1)
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue (HashMapUr)
import Data.Record.Linear
import Data.UnionFind.Linear.Borrowed (UnionFind)
import Data.Unrestricted.Linear.Lifted (Copyable1)
import Data.Vector.Unboxed.Mutable.Growable.Borrowed qualified as BUV
import GHC.Generics (Generic, Generically (..))
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Text.Show.Borrowed (Display)
import Prelude qualified as P

{- | Invariant: all the 'EClassId's appearing somewhere in this structure
  must be valid keys in the 'unionFind' field.
-}
data EGraph d l = EGraph
  { unionFind :: !UnionFind
  -- ^ A union-find structure on e-class ids.
  , classes :: !(EClasses d l)
  {- ^ A mapping from EClassId to EClass.

  Invariant: only the canonical EClassIds resides in the e-class.
  -}
  , nodes :: !(HashMapUr EClassId (ENode l))
  {- ^ A map from eclass-id to the _original_ enode.
  Associated e-node MUST BE canonical AFTER rebuilding.

  NOTE: this field is not mentioned in the original egg paper,
  but it is needed to recover the hashcons invariant on the nodes
  that are being unioned.
  -}
  , hashcons :: !(HashMapUr (ENode l) EClassId)
  {- ^
  A map from _canonical_ enodes to eclass-ids.
  Keys MUST BE canonical AFTER rebuilding.
  -}
  , worklist :: !(BUV.Vector EClassId)
  -- ^ A set of eclass-ids that need to be repaired.
  }
  deriving (Generic)

deriveGeneric ''EGraph

deriving anyclass instance SplittableRecord (EGraph l d)

deriving via
  Generically (EGraph d l)
  instance
    (Copyable1 l, Show1 l, Display d) => Display (EGraph d l)

deriving via Generically (EGraph d l) instance Consumable (EGraph d l)

deriving via Generically (EGraph d l) instance (Dupable d) => Dupable (EGraph d l)

hashconsL :: RecordLabel (EGraph d l) "hashcons" (HashMapUr (ENode l) EClassId)
hashconsL = #hashcons

{- |
Analysis is a meet-semilattice @d@ (although it is called _join_ in the original paper),
with additional operations to make an analysis on e-graphs classes.
In addition to 'Semilattice' laws, it must satisfy the following laws:

  1. Idempotency of modify: @'modify' eid =<< 'modify' eid egraph == modify eid egraph@.
-}
class (P.Traversable l, Semilattice d, Copyable d, Movable d) => Analysis l d where
  makeAnalysis :: l (EClassId, d) -> d
  modifyAnalysis ::
    (Analysis l d') =>
    Lens' d' d -> EClassId -> Mut α (EGraph d' l) %1 -> BO α ()
  modifyAnalysis = const $ const $ Control.pure . consume

instance (P.Traversable l) => Analysis l () where
  makeAnalysis _ = ()

instance LinearOnly (EGraph d l) where
  linearOnly = UnsafeLinearOnly

instance (Analysis l a, Analysis l b) => Analysis l (a, b) where
  makeAnalysis xs = (makeAnalysis (Bi.second fst P.<$> xs), makeAnalysis (Bi.second snd P.<$> xs))
  modifyAnalysis l eid egraph = Control.do
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _1) eid
    modifyAnalysis (l P.. _2) eid egraph

instance (Analysis l a, Analysis l b, Analysis l c) => Analysis l (a, b, c) where
  makeAnalysis xs =
    ( makeAnalysis (Bi.second (view _1) P.<$> xs)
    , makeAnalysis (Bi.second (view _2) P.<$> xs)
    , makeAnalysis (Bi.second (view _3) P.<$> xs)
    )
  modifyAnalysis l eid egraph = Control.do
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _1) eid
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _2) eid
    modifyAnalysis (l P.. _3) eid egraph

instance (Analysis l a, Analysis l b, Analysis l c, Analysis l d) => Analysis l (a, b, c, d) where
  makeAnalysis xs =
    ( makeAnalysis (Bi.second (view _1) P.<$> xs)
    , makeAnalysis (Bi.second (view _2) P.<$> xs)
    , makeAnalysis (Bi.second (view _3) P.<$> xs)
    , makeAnalysis (Bi.second (view _4) P.<$> xs)
    )
  modifyAnalysis l eid egraph = Control.do
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _1) eid
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _2) eid
    egraph <- reborrowing_ egraph $ modifyAnalysis (l P.. _3) eid
    modifyAnalysis (l P.. _4) eid egraph
