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

  -- * Scheduler (re-exports)
  BackoffScheduler (..),
  defaultScheduler,
) where

import Algebra.Semilattice
import Control.DeepSeq
import Control.Exception (Exception)
import Control.Functor.Linear qualified as Control
import Control.Lens (Lens', (?~), (^.), _1)
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Clone
import Control.Monad.Borrow.Pure.Experimental.Loop
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Deriving (deriveShow1)
import Data.EGraph.EMatch.Relational (ematchDbWithCount)
import Data.EGraph.EMatch.Relational.Database (buildDatabaseForPatterns)
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution (..), substPattern)
import Data.EGraph.Saturation.Scheduler
import Data.EGraph.Types
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.Language
import Data.Foldable qualified as F
import Data.Function ((&))
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as PHM
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty qualified as NE
import Data.Record.Linear.Borrow.Experimental.PatternMatch
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as Ref
import Data.Semigroup (Arg (..), ArgMin, Min (..))
import Data.Strict qualified as St
import Data.Traversable qualified as Traverse
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics (Generic, Generic1)
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear (lseq)
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
  deriving (Eq, Ord, Generic, Generic1, Functor, P.Foldable, Traversable)

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
  deriving (Show, GHC.Generic)

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
  , scheduler :: !(Maybe BackoffScheduler)
  {- ^ Optional backoff scheduler to prevent rule explosion.
  When 'Nothing', no scheduling is applied (all rules run every iteration).
  When 'Just', rules that produce too many matches get temporarily banned.
  -}
  }
  deriving (Show, Eq, Ord, Generic)

defaultConfig :: SaturationConfig
defaultConfig =
  SaturationConfig
    { maxIterations = Just 30
    , nodeLimit = Just 10_000
    , scheduler = Just defaultScheduler
    }

{-# INLINEABLE saturate #-}
saturate ::
  forall d l v α.
  (Analysis l d, Language l, Hashable v) =>
  SaturationConfig ->
  [CompiledRule l d v] ->
  Mut α (EGraph d l) %1 ->
  BO α (Mut α (EGraph d l))
saturate config rules = go 0 initialState (St.toStrict config.maxIterations)
  where
    indexedRules :: [(Int, CompiledRule l d v)]
    indexedRules = zip [0 ..] rules

    needsSelectAll :: Bool
    needsSelectAll = any isSelectAllRule rules

    isSelectAllRule CompiledRule {lhs = PatternQuery {patQuery = SelectAll {}}} = True
    isSelectAllRule _ = False

    go ::
      Int ->
      SchedulerState ->
      St.Maybe Word ->
      Mut α (EGraph d l) %1 ->
      BO α (Mut α (EGraph d l))
    go !_ !_ (St.Just 0) !egraph = Control.pure egraph
    go !iterNum !schedState remaining egraph = Control.do
      (Ur currentSize, egraph) <- size <$~ egraph
      (Ur numClasses, egraph) <- numEClasses <$~ egraph
      if maybe False (currentSize >) config.nodeLimit
        then Control.pure egraph
        else Control.do
          (Ur (results, matchCounts, schedSearched), egraph) <- sharing egraph \egraph -> Control.do
            Ur db <- buildDatabaseForPatterns needsSelectAll egraph
            -- Match all non-banned rules against one immutable database.
            -- Side conditions are deliberately NOT checked here: hegg checks
            -- each condition immediately before applying its match, against
            -- the graph produced by all preceding applications in this
            -- iteration.  Freezing condition data in the read phase delays
            -- analysis-dependent rewrites by an iteration and materially
            -- changes the backoff trajectory on expansive rule sets.
            let searchOne (accRaws, st) (ruleIdx, rule@CompiledRule {..}) =
                  case config.scheduler of
                    Nothing ->
                      let (ms, stat) = ematchDbWithCount lhs db
                       in ((ruleIdx, rule, ms, stat) : accRaws, st)
                    Just sched
                      | isBanned iterNum ruleIdx st ->
                          ((ruleIdx, rule, [], 0) : accRaws, st)
                      | sched.deferOverLimitMatches ->
                          -- egg's search_rewrite: an over-threshold rule is
                          -- banned NOW and its matches are dropped for this
                          -- iteration (deferred to a later re-match). The
                          -- statistic is egg's: the number of substitutions.
                          let (ms, _stat) = ematchDbWithCount lhs db
                           in case banAtSearch sched iterNum ruleIdx (P.length ms) st of
                                Just st' -> ((ruleIdx, rule, [], 0) : accRaws, st')
                                Nothing -> ((ruleIdx, rule, ms, 0) : accRaws, st)
                      | otherwise ->
                          let (ms, rawSubstitutionSize) = ematchDbWithCount lhs db
                           in -- NB: apply ALL matches of a non-banned rule (as
                              -- hegg does); the scheduler statistic only
                              -- feeds the backoff, which bans over-productive
                              -- rules on LATER iterations. The statistic is
                              -- hegg-compatible: the exact sum of the emitted
                              -- internal substitution sizes.
                              ((ruleIdx, rule, ms, rawSubstitutionSize) : accRaws, st)
                (rawsRev, stSearched) = F.foldl' searchOne ([], schedState) indexedRules
                (resultsL, countsL) = collect (P.reverse rawsRev)
            Control.pure (Ur (resultsL, countsL, stSearched))
          if null results
            then -- A stall with rules still banned is not saturation under
            -- egg semantics: shift the bans and keep iterating.
              case config.scheduler of
                Just sched
                  | sched.deferOverLimitMatches
                  , Just schedState'' <- canStop iterNum schedSearched ->
                      go (iterNum + 1) schedState'' (subtract 1 <$> remaining) egraph
                _ -> Control.pure egraph
            else Control.do
              (Ur _, egraph) <- substitute egraph results
              -- Update scheduler state based on match counts. In deferring
              -- (egg) mode the bans were already applied during the search.
              let !schedState' = case config.scheduler of
                    Nothing -> schedState
                    Just sched
                      | sched.deferOverLimitMatches -> schedSearched
                      | otherwise -> updateStats sched iterNum matchCounts schedState
              -- hegg rebuilds every nonempty application batch before deciding
              -- whether saturation was reached.  Counts can be unchanged while
              -- congruence or analysis work is still pending.
              egraph <- rebuild egraph
              (Ur currentSize', egraph) <- size <$~ egraph
              (Ur numClasses', egraph) <- numEClasses <$~ egraph
              if currentSize' /= currentSize || numClasses' /= numClasses
                then go (iterNum + 1) schedState' (subtract 1 <$> remaining) egraph
                else case config.scheduler of
                  Just sched
                    | sched.deferOverLimitMatches
                    , Just schedState'' <- canStop iterNum schedState' ->
                        go (iterNum + 1) schedState'' (subtract 1 <$> remaining) egraph
                  _ -> Control.pure egraph

    -- Pair every raw match with its rule. Conditions are checked in the
    -- write phase, just before application, matching hegg's semantics.
    collect ::
      [(Int, CompiledRule l d v, [(EClassId, Substitution v)], Int)] ->
      ([Ur (EClassId, Substitution v, CompiledRule l d v)], [(Int, Int)])
    collect raws =
      let (matchesList, countsList) = unzip $ flip map raws \(ruleIdx, rule, ms, stat) ->
            (map (\(eid, subs) -> Ur (eid, subs, rule)) ms, (ruleIdx, stat))
       in (concat matchesList, countsList)

    substitute ::
      Mut α (EGraph d l) %1 ->
      [Ur (EClassId, Substitution v, CompiledRule l d v)] %1 ->
      BO α (Ur Bool, Mut α (EGraph d l))
    substitute egraph results = reborrowing' egraph \egraph -> Control.do
      !(var, lend) <- borrowLinearlyM (Ref.new False)
      varEGraph <-
        forReborrowing_
          (var :- egraph :- BNil)
          results
          \(var :- egraph :- BNil) (Ur (eid, subs, CompiledRule {..})) ->
            Control.do
              (Ur shouldApply, egraph) <- sharing egraph \egraph ->
                case condition of
                  Nothing -> Control.pure (Ur True)
                  Just (SideCondition cond) -> Control.do
                    let !neededIds = HashSet.toList $ HashSet.fromList $ PHM.elems subs.substitution
                    Ur infos <- lookupMatchInfos neededIds egraph
                    let !matchInfos =
                          PHM.mapMaybeWithKey
                            ( \_ eclassId -> do
                                (nodes, analysis) <- PHM.lookup eclassId infos
                                Just MatchInfo {..}
                            )
                            subs.substitution
                    Control.pure (Ur (cond matchInfos))
              if shouldApply
                then case substPattern subs rhs of
                  Failure _ -> var `lseq` egraph `lseq` error "Substitution produces invalid expression"
                  Success pat -> Control.do
                    (Ur newEid, egraph) <- addNestedENode pat egraph
                    -- Hegg applies a variable RHS as @merge variable lhs@,
                    -- while a node RHS is applied as @merge lhs node@.  The
                    -- distinction is observable: equal parent counts retain
                    -- the first argument as the union-find representative.
                    (Ur resl, egraph) <- case pat of
                      Metavar {} -> unsafeMerge newEid eid egraph
                      PNode {} -> unsafeMerge eid newEid egraph
                    case resl of
                      Merged {} -> Control.void PL.$ Ref.modify (`lseq` True) var
                      AlreadyMerged {} -> Control.pure PL.$ consume var
                    Control.pure (consume egraph)
                else Control.pure (consume var `lseq` consume egraph)
      case varEGraph of
        var :- egraph :- BNil ->
          Control.pure PL.$
            upcast PL.$
              var `lseq`
                egraph `lseq`
                  (move PL.. Ref.free Control.<$> reclaim' lend)

addNestedENode ::
  forall d l α.
  (Analysis l d, Hashable1 l) =>
  Pattern l EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur EClassId, Mut α (EGraph d l))
{-# INLINE addNestedENode #-}
addNestedENode pat egraph = go pat egraph
  where
    -- Direct BO-level recursion threading the e-graph explicitly instead of
    -- an UrT-over-StateT tower: no per-node transformer plumbing.
    go ::
      Pattern l EClassId ->
      Mut α (EGraph d l) %1 ->
      BO α (Ur EClassId, Mut α (EGraph d l))
    go (Metavar eid) egraph = sharing egraph \egraph -> unsafeFind egraph eid
    go (PNode p) egraph = Control.do
      (Ur eids, egraph) <- goChildren (F.toList p) [] egraph
      addCanonicalNode (ENode (refill p eids)) egraph

    goChildren ::
      [Pattern l EClassId] ->
      [EClassId] ->
      Mut α (EGraph d l) %1 ->
      BO α (Ur [EClassId], Mut α (EGraph d l))
    goChildren [] acc egraph = Control.pure (Ur (P.reverse acc), egraph)
    goChildren (p : ps) acc egraph = Control.do
      (Ur eid, egraph) <- go p egraph
      goChildren ps (eid : acc) egraph

{- | Canonicalize the keys in the analyses map.
This is necessary because e-matching returns canonical e-class ids,
but the analyses map from EC.analyses uses original ids.
After merges, we need to ensure lookups by canonical id succeed.
-}
{-# INLINEABLE lookupMatchInfos #-}
lookupMatchInfos ::
  forall d l bk α m.
  [EClassId] ->
  Borrow bk α (EGraph d l) %m ->
  BO α (Ur (PHM.HashMap EClassId ([ENode l], d)))
lookupMatchInfos eids egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    let go ::
          [EClassId] ->
          PHM.HashMap EClassId ([ENode l], d) ->
          BO α (Ur (PHM.HashMap EClassId ([ENode l], d)))
        go [] acc = Control.pure (Ur acc)
        go (eid : rest) acc = Control.do
          Ur mnodes <- lookupEClass eid egraph
          Ur manal <- getAnalysis eid egraph
          case (,) P.<$> mnodes P.<*> manal of
            Nothing -> go rest acc
            Just (nodes, anal) ->
              go rest (PHM.insert eid (NE.toList nodes, anal) acc)
    go eids PHM.empty

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
  AsCopyable (ExtractBest l cost)
  instance
    ( Copyable1 l
    , Copyable cost
    ) =>
    Clone (ExtractBest l cost)

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
  (Language l) =>
  EClassId ->
  Borrow k α (EGraph (ExtractBest l cost) l) %m ->
  BO α (Ur (Maybe (Term l, cost)))
extractBest_ = extractBestOf id

{- | Extract the best term from the given e-class minimizing the given cost model, using given lens.
To get the maximal term, use 'Data.Ord.Down' as the cost type.
-}
extractBest ::
  (Language l) =>
  EClassId ->
  Borrow k α (EGraph (ExtractBest l cost, d) l) %m ->
  BO α (Ur (Maybe (Term l, cost)))
extractBest = extractBestOf _1

{- | Extract the best term from the given e-class minimizing the given cost model, using given lens.
To get the maximal term, use 'Data.Ord.Down' as the cost type.
-}
extractBestOf ::
  (Language l) =>
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
