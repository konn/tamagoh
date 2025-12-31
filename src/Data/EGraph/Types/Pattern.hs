{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.Pattern (
  Pattern (..),
  matchOneStep,
  matchNode,
  embedTerm,
  addPattern,
) where

import Control.Functor.Linear (StateT (..))
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EGraph (EGraph, addNode, find)
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Language
import Data.FMList qualified as FML
import Data.Fix (Fix (unFix))
import Data.Foldable qualified as F
import Data.Functor.Classes (Eq1, Ord1, Show1)
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Movable1)
import GHC.Generics (Generically1)
import GHC.Generics qualified as GHC
import Prelude.Linear (Ur)
import Prelude.Linear qualified as PL
import Text.Show.Deriving (deriveShow1)
import Prelude as P

data Pattern l v = Metavar v | PNode (l (Pattern l v))
  deriving (GHC.Generic, GHC.Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable1)
  deriving (Eq1, Ord1) via Generically1 (Pattern l)

deriving anyclass instance (Hashable1 l, Hashable v) => Hashable (Pattern l v)

deriving stock instance (Show1 l, Show v) => Show (Pattern l v)

deriving stock instance (Eq1 l, Eq v) => Eq (Pattern l v)

deriving stock instance (Ord1 l, Ord v) => Ord (Pattern l v)

deriveShow1 ''Pattern

embedTerm :: (Functor l) => Term l -> Pattern l v
embedTerm = PNode . fmap embedTerm . unwrapTerm

matchOneStep :: (Matchable l) => Pattern l v -> Term l -> Maybe [(Pattern l v, Term l)]
matchOneStep p@Metavar {} = Just . pure . (p,)
matchOneStep (PNode p) = fmap (F.toList) . tryMatch p . unFix

matchNode ::
  (Matchable l) =>
  Pattern l v -> ENode l -> Maybe (Either (v, ENode l) [(Pattern l v, EClassId)])
matchNode (Metavar v) node = Just $ Left (v, node)
matchNode (PNode p) (ENode node) = Right . FML.toList <$> tryMatch p node

addPattern ::
  forall l α.
  (Traversable l, Hashable1 l, Movable1 l) =>
  Pattern l EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph l))
addPattern pat egraph =
  PL.flip Control.runStateT egraph PL.$ runUrT PL.$ runMaybeT do
    go pat
  where
    go ::
      Pattern l EClassId ->
      MaybeT (UrT (StateT (Mut α (EGraph l)) (BO α))) EClassId
    go (Metavar eid) = MaybeT PL.$ UrT PL.$ StateT \egraph ->
      sharing egraph \egraph -> find egraph eid
    go (PNode p) = do
      eids <- ENode <$> P.traverse go p
      MaybeT PL.$ UrT PL.$ StateT \egraph -> addNode egraph eids
