{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.Pattern (
  Pattern (..),
  matchOneStep,
  matchNode,
  embedTerm,
) where

import Control.DeepSeq (NFData, NFData1)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EGraph
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Term
import Data.FMList qualified as FML
import Data.Foldable qualified as F
import Data.Functor.Classes (Eq1, Ord1, Show1)
import Data.Functor.Foldable (Base, Corecursive (..))
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import GHC.Generics (Generically1)
import GHC.Generics qualified as GHC
import Text.Show.Deriving (deriveShow1)
import Prelude as P

data Pattern l v = Metavar v | PNode (l (Pattern l v))
  deriving (GHC.Generic, GHC.Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable1, NFData1)
  deriving (Eq1, Ord1) via Generically1 (Pattern l)

deriving anyclass instance (NFData1 l, NFData v) => NFData (Pattern l v)

deriving anyclass instance (Hashable1 l, Hashable v) => Hashable (Pattern l v)

deriving stock instance (Show1 l, Show v) => Show (Pattern l v)

deriving stock instance (Eq1 l, Eq v) => Eq (Pattern l v)

deriving stock instance (Ord1 l, Ord v) => Ord (Pattern l v)

deriveShow1 ''Pattern

type instance Base (Pattern l v) = l

instance (Functor l) => Corecursive (Pattern l v) where
  embed = PNode

embedTerm :: (Functor l) => Term l -> Pattern l v
embedTerm = PNode . fmap embedTerm . unwrapTerm

matchOneStep :: (Matchable l) => Pattern l v -> Term l -> Maybe [(Pattern l v, Term l)]
matchOneStep p@Metavar {} = Just . pure . (p,)
matchOneStep (PNode p) = fmap (F.toList) . tryMatch p . unwrapTerm

matchNode ::
  (Matchable l) =>
  Pattern l v -> ENode l -> Maybe (Either (v, ENode l) [(Pattern l v, EClassId)])
matchNode (Metavar v) node = Just $ Left (v, node)
matchNode (PNode p) (ENode node) = Right . FML.toList <$> tryMatch p node
