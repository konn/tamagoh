{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Saturation (
  saturate,
  Rule (..),
  CompiledRule,
  compileRule,
  (==>),
) where

import Control.Exception (Exception)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Utils (forRebor_)
import Control.Monad.Trans.Writer.CPS (execWriter, tell)
import Data.Deriving (deriveShow1)
import Data.EGraph.EMatch.Relational (ematchDb)
import Data.EGraph.EMatch.Relational.Database (Database, HasDatabase, buildDatabase)
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution, substPattern)
import Data.EGraph.Types
import Data.FMList qualified as FML
import Data.Foldable qualified as F
import Data.Foldable qualified as P
import Data.Functor.Classes
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Hashable.Lifted (Hashable1)
import Data.Strict qualified as St
import GHC.Generics (Generic)
import GHC.Generics qualified as GHC
import Prelude.Linear (Consumable (consume), Ur (..), consume)
import Prelude.Linear qualified as PL
import Validation (Validation (..))

data Rule l v = Rule
  { lhs :: !(Pattern l v)
  , rhs :: !(Pattern l v)
  , name :: !String
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, GHC.Generic, GHC.Generic1)
  deriving (Eq1, Ord1) via GHC.Generically1 (Rule l)
  deriving anyclass (Hashable, Hashable1)

deriveShow1 ''Rule

infix 5 ==>

(==>) :: (Show1 l, Show v) => Pattern l v -> Pattern l v -> Rule l v
lhs ==> rhs =
  let !name = showsPrec 11 lhs . showString " ==> " . showsPrec 11 rhs $ ""
   in Rule {name, ..}

data CompiledRule l v = CompiledRule
  { name :: !String
  , lhs :: !(PatternQuery l v)
  , rhs :: !(Pattern l v)
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, GHC.Generic, GHC.Generic1)
  deriving (Eq1, Ord1) via GHC.Generically1 (CompiledRule l)
  deriving anyclass (Hashable, Hashable1)

data SaturationError l v = DanglingVariables (HashSet.HashSet v)
  deriving (Show, Eq, Ord)
  deriving anyclass (Exception)

compileRule ::
  (Traversable l, Hashable v) =>
  Rule l v ->
  Either (SaturationError l v) (CompiledRule l v)
compileRule Rule {..} = do
  let danglings =
        HashSet.fromList (F.toList rhs)
          `HashSet.difference` HashSet.fromList (F.toList lhs)

  if HashSet.null danglings
    then pure CompiledRule {lhs = compile lhs, ..}
    else Left $ DanglingVariables danglings

data SaturationConfig = SaturationConfig
  { maxIterations :: {-# UNPACK #-} !(Maybe Word)
  }
  deriving (Show, Eq, Ord, Generic)

saturate ::
  forall l v α.
  (Language l, HasDatabase l, Hashable v) =>
  SaturationConfig ->
  [CompiledRule l v] ->
  Mut α (EGraph l) %1 ->
  BO α (Mut α (EGraph l))
saturate config rules = go (St.toStrict config.maxIterations)
  where
    go :: St.Maybe Word -> Mut α (EGraph l) %1 -> BO α (Mut α (EGraph l))
    go (St.Just 0) !egraph = Control.pure egraph
    go remaining !egraph = Control.do
      (Ur results, egraph) <- sharing egraph \egraph -> Control.do
        Ur db <- buildDatabase egraph
        Control.pure (Ur $ collect db)
      if null results
        then Control.pure egraph
        else Control.do
          egraph <- substitute egraph results
          egraph <- rebuild egraph
          go (subtract 1 <$> remaining) egraph

    collect :: Database l -> [Ur (EClassId, Substitution v, CompiledRule l v)]
    collect db = FML.toList $ execWriter do
      P.forM_ rules \rule@CompiledRule {..} -> Control.do
        let matches = ematchDb lhs db
        tell $! FML.fromList $ map (\(eid, subs) -> Ur (eid, subs, rule)) matches

    substitute ::
      Mut α (EGraph l) %1 ->
      [Ur (EClassId, Substitution v, CompiledRule l v)] %1 ->
      BO α (Mut α (EGraph l))
    substitute egraph results = forRebor_
      egraph
      results
      \egraph (Ur (eid, subs, CompiledRule {..})) ->
        case substPattern subs rhs of
          Failure _ -> Control.pure PL.$ consume egraph
          Success pat -> Control.do
            (Ur meid, egraph) <- addPattern pat egraph
            meid PL.& \case
              Nothing -> Control.pure PL.$ consume egraph
              Just newEid -> Control.do
                (Ur _, egraph) <- merge eid newEid egraph
                Control.pure PL.$ consume egraph