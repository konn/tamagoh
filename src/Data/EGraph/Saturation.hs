{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Saturation (
  saturate,
  extractBest,
  extractBest_,
  extractBestOf,
  SaturationConfig (..),
  defaultConfig,
  SaturationError (..),
  Rule (..),
  (==>),
  (@?),
  named,
  CompiledRule,
  compileRule,
  ExtractBest (..),
  CostModel (..),
  SideCondition (..),
  MatchInfo (..),
) where

import Algebra.Semilattice
import Control.DeepSeq
import Control.Exception (Exception)
import Control.Functor.Linear (StateT (..))
import Control.Functor.Linear qualified as Control
import Control.Lens (Lens', (?~), (^.), _1)
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils (forRebor2_)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Writer.CPS (execWriter, tell)
import Data.Coerce.Directed (upcast)
import Data.Deriving (deriveShow1)
import Data.EGraph.EMatch.Relational (ematchDb)
import Data.EGraph.EMatch.Relational.Database (Database, buildDatabase)
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution (..), substPattern)
import Data.EGraph.Types
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.Language
import Data.FMList qualified as FML
import Data.Foldable qualified as F
import Data.Foldable qualified as P
import Data.Function ((&))
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HasField.Linear
import Data.HashMap.Strict qualified as PHM
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Hashable.Lifted (Hashable1)
import Data.Maybe (mapMaybe)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Semigroup (Arg (..), ArgMin, Min (..))
import Data.Strict qualified as St
import Data.Traversable qualified as Traverse
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics (Generic, Generic1)
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear (Consumable (consume), Dupable, Movable, Ur (..), consume, lseq)
import Prelude.Linear qualified as PL
import Text.Show.Borrowed (AsCopyableShow (..), Display)
import Validation (Validation (..))
import Prelude as P

newtype SideCondition l d v = SideCondition (PHM.HashMap v (MatchInfo l d) -> Bool)
  deriving (Generic)
  deriving anyclass (NFData)

data MatchInfo l d = MatchInfo
  { eclassId :: EClassId
  , nodes :: ![ENode l]
  , analysis :: !d
  }
  deriving (Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)

instance Show (SideCondition l d v) where
  showsPrec _ _ = showString "<side condition>"

instance Show1 (SideCondition l d) where
  liftShowsPrec _ _ _ _ = showString "<side condition>"

data Rule l d v = Rule
  { lhs :: !(Pattern l v)
  , rhs :: !(Pattern l v)
  , condition :: Maybe (SideCondition l d v)
  , name :: !String
  }
  deriving (Show, GHC.Generic, GHC.Generic1)
  deriving anyclass (NFData)

deriveShow1 ''Rule

named :: String -> Rule l d v -> Rule l d v
named name Rule {lhs, rhs, condition} = Rule {..}

infix 5 ==>

(==>) :: (Show1 l, Show v) => Pattern l v -> Pattern l v -> Rule l d v
lhs ==> rhs =
  let !name = showsPrec 11 lhs . showString " ==> " . showsPrec 11 rhs $ ""
      !condition = Nothing
   in Rule {name, ..}

infix 1 @?

(@?) ::
  Rule l d0 v ->
  (PHM.HashMap v (MatchInfo l d) -> Bool) ->
  Rule l d v
r @? cond = r & #condition ?~ SideCondition cond

data CompiledRule l d v = CompiledRule
  { name :: !String
  , lhs :: !(PatternQuery l v)
  , rhs :: !(Pattern l v)
  , condition :: !(Maybe (SideCondition l d v))
  }
  deriving (Show, GHC.Generic, GHC.Generic1)

data SaturationError l v = DanglingVariables (HashSet.HashSet v)
  deriving (Show, Eq, Ord)
  deriving anyclass (Exception)

compileRule ::
  (Traversable l, Hashable v) =>
  Rule l d v ->
  Either (SaturationError l v) (CompiledRule l d v)
compileRule Rule {..} = do
  let danglings =
        HashSet.fromList (F.toList rhs)
          `HashSet.difference` HashSet.fromList (F.toList lhs)

  if HashSet.null danglings
    then pure CompiledRule {lhs = compile lhs, ..}
    else Left $ DanglingVariables danglings

data SaturationConfig = SaturationConfig
  { maxIterations :: {-# UNPACK #-} !(Maybe Word)
  , nodeLimit :: {-# UNPACK #-} !(Maybe Int)
  }
  deriving (Show, Eq, Ord, Generic)

defaultConfig :: SaturationConfig
defaultConfig = SaturationConfig {maxIterations = Just 30, nodeLimit = Just 10_000}

saturate ::
  forall d l v α.
  (Analysis l d, Language l, Show1 l, Hashable v, Show v) =>
  SaturationConfig ->
  [CompiledRule l d v] ->
  Mut α (EGraph d l) %1 ->
  BO α (Mut α (EGraph d l))
saturate config rules = go (St.toStrict config.maxIterations)
  where
    go :: St.Maybe Word -> Mut α (EGraph d l) %1 -> BO α (Mut α (EGraph d l))
    go (St.Just 0) !egraph = Control.pure egraph
    go remaining egraph = Control.do
      (Ur size, egraph) <- size <$~ egraph
      if maybe False (size >) config.nodeLimit
        then Control.pure egraph
        else Control.do
          (Ur results, egraph) <- sharing egraph \egraph -> Control.do
            Ur db <- buildDatabase egraph
            Ur anals <- EC.analyses (egraph .# #classes)
            Control.pure (Ur $ collect anals db)
          if null results
            then Control.pure egraph
            else Control.do
              (progress, egraph) <- substitute egraph results
              if progress
                then Control.do
                  egraph <- rebuild egraph
                  go (subtract 1 <$> remaining) egraph
                else Control.pure egraph

    collect ::
      PHM.HashMap EClassId ([ENode l], d) ->
      Database l ->
      [Ur (EClassId, Substitution v, CompiledRule l d v)]
    collect analyses db =
      FML.toList $! execWriter do
        P.forM_ rules \rule@CompiledRule {..} -> do
          let matches = ematchDb lhs db
          tell . FML.fromList $ mapMaybe (check analyses rule) matches

    check analyses rule (eid, subs) =
      case rule.condition of
        Just (SideCondition cond)
          | not $
              cond
                ( PHM.mapMaybe
                    ( \eclassId -> do
                        (nodes, analysis) <- PHM.lookup eclassId analyses
                        Just MatchInfo {..}
                    )
                    subs.substitution
                ) ->
              Nothing
        _ -> Just $ Ur (eid, subs, rule)

    substitute ::
      Mut α (EGraph d l) %1 ->
      [Ur (EClassId, Substitution v, CompiledRule l d v)] %1 ->
      BO α (Bool, Mut α (EGraph d l))
    substitute egraph results = reborrowing' egraph \egraph -> Control.do
      !(var, lend) <- asksLinearly PL.$ borrowLinearOnly PL.. Ref.new False
      (var, egraph) <- forRebor2_ var egraph results \var egraph (Ur (eid, subs, CompiledRule {..})) ->
        case substPattern subs rhs of
          Failure _ -> var `lseq` egraph `lseq` error "Substitution produces invalid expression"
          Success pat -> Control.do
            (Ur newEid, egraph) <- addNestedENode pat egraph
            (Ur resl, egraph) <- unsafeMerge eid newEid egraph
            case resl of
              Merged {} -> Control.void PL.$ modifyRef (`lseq` True) var
              AlreadyMerged {} -> Control.pure PL.$ consume var
            Control.pure (consume egraph)
      Control.pure \end -> var `lseq` egraph `lseq` freeRef (reclaim lend (upcast end))

addNestedENode ::
  forall d l α.
  (Analysis l d, Hashable1 l, Movable1 l) =>
  Pattern l EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur EClassId, Mut α (EGraph d l))
{-# INLINE addNestedENode #-}
addNestedENode pat egraph =
  Control.runStateT (runUrT PL.$ go pat) egraph
  where
    go ::
      Pattern l EClassId ->
      UrT (StateT (Mut α (EGraph d l)) (BO α)) EClassId
    go (Metavar eid) = UrT PL.$ StateT \egraph -> sharing egraph \egraph -> unsafeFind egraph eid
    go (PNode p) = do
      eids <- ENode <$> P.traverse go p
      UrT PL.$ StateT \egraph -> addCanonicalNode eids egraph

newtype ExtractBest l cost = ExtractBest
  { optimal :: ArgMin cost (ENode l)
  }
  deriving (Eq, Ord, Show, Generic)
  deriving newtype (Semilattice)

deriveGeneric ''ExtractBest

deriving via
  GHC.Generically (ExtractBest l cost)
  instance
    ( Copyable1 l
    , Copyable cost
    ) =>
    Copyable (ExtractBest l cost)

deriving via
  GHC.Generically (ExtractBest l cost)
  instance
    ( Movable1 l
    , Consumable cost
    ) =>
    Consumable (ExtractBest l cost)

deriving via
  GHC.Generically (ExtractBest l cost)
  instance
    ( Movable1 l
    , Dupable cost
    ) =>
    Dupable (ExtractBest l cost)

deriving via
  GHC.Generically (ExtractBest l cost)
  instance
    ( Movable1 l
    , Movable cost
    ) =>
    Movable (ExtractBest l cost)

deriving via
  AsCopyableShow (ExtractBest l cost)
  instance
    (Show cost, Copyable cost, Show1 l, Copyable1 l) => Display (ExtractBest l cost)

class
  ( Ord cost
  , Copyable cost
  , Movable cost
  ) =>
  CostModel cost l
  where
  costFunction :: l (Min cost) -> Min cost

instance
  ( CostModel cost l
  , Copyable1 l
  , Movable1 l
  , Traversable l
  ) =>
  Analysis l (ExtractBest l cost)
  where
  makeAnalysis node =
    let enode = ENode $ fst <$> node
        Min !cost = costFunction (fmap (\(Arg w _) -> w) . (.optimal) . snd <$> node)
     in ExtractBest $ Min (Arg cost enode)

{- | Extract the best term from the given e-class minimizing the given cost model, using given lens.
To get the maximal term, use 'Data.Ord.Down' as the cost type.
-}
extractBest_ ::
  (Language l, CostModel cost l) =>
  EClassId ->
  Borrow k α (EGraph (ExtractBest l cost) l) %m ->
  BO α (Ur (Maybe (Term l, cost)))
extractBest_ = extractBestOf id

{- | Extract the best term from the given e-class minimizing the given cost model, using given lens.
To get the maximal term, use 'Data.Ord.Down' as the cost type.
-}
extractBest ::
  (Analysis l d, Language l, CostModel cost l) =>
  EClassId ->
  Borrow k α (EGraph (ExtractBest l cost, d) l) %m ->
  BO α (Ur (Maybe (Term l, cost)))
extractBest = extractBestOf _1

{- | Extract the best term from the given e-class minimizing the given cost model, using given lens.
To get the maximal term, use 'Data.Ord.Down' as the cost type.
-}
extractBestOf ::
  (Analysis l d, Language l) =>
  Lens' d (ExtractBest l cost) ->
  EClassId ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe (Term l, cost)))
extractBestOf costL eid egraph =
  share egraph PL.& \(Ur egraph) ->
    let go eid = do
          eid <- MaybeT $ UrT $ find egraph eid
          anal <- MaybeT $ UrT PL.$ EC.lookupAnalysis (egraph .# #classes) eid
          let Min (Arg cost (ENode node)) = anal ^. costL . #optimal
          term <- Traverse.mapM (fmap fst . go) node
          pure (wrapTerm term, cost)
     in runUrT PL.$ runMaybeT $ go eid
