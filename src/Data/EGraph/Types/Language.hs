{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EGraph.Types.Language (
  Language,
  Term,
  wrapTerm,
  unwrapTerm,
  Matchable (..),
  GenericMatchable,
  genericTryMatch,
) where

import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.Types.Term
import Data.Hashable.Lifted (Hashable1)
import Data.Traversable qualified as P
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)

type Language l = (Hashable1 l, Movable1 l, P.Traversable l, Matchable l, Copyable1 l, HasDatabase l)
