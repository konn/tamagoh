{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.EGraph.Saturation (
  Rule (..),
  (==>),
) where

import Data.Deriving (deriveShow1)
import Data.EGraph.Types.Pattern
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted (Hashable1)
import GHC.Generics qualified as GHC

data Rule l v = Rule
  { lhs :: Pattern l v
  , rhs :: Pattern l v
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, GHC.Generic, GHC.Generic1)
  deriving (Eq1, Ord1) via GHC.Generically1 (Rule l)
  deriving anyclass (Hashable, Hashable1)

deriveShow1 ''Rule

infix 5 ==>

(==>) :: Pattern l v -> Pattern l v -> Rule l v
(==>) = Rule
