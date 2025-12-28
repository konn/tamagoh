{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.EGraph.Types.Pattern (
  Pattern (..),
  matchOneStep,
  matchNode,
  embedTerm,
) where

import Data.EGraph.Types.EClassId
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Language
import Data.FMList qualified as FML
import Data.Fix (Fix (unFix))
import Data.Foldable qualified as F
import Data.Functor.Classes (Eq1, Ord1, Show1)
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import GHC.Generics (Generically1)
import GHC.Generics qualified as GHC
import Text.Show.Deriving (deriveShow1)

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
