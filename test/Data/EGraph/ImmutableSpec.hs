{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.ImmutableSpec (module Data.EGraph.ImmutableSpec) where

import Algebra.Semilattice
import Control.Exception (throwIO)
import Control.Functor.Linear qualified as Control
import Control.Lens (view)
import Control.Monad.Borrow.Pure (Copyable, (<$~))
import Control.Monad.Borrow.Pure.Clone
import Data.EGraph.EMatch.Relational qualified as Rel
import Data.EGraph.EMatch.Relational.Database (Database)
import Data.EGraph.EMatch.Relational.Query qualified as Q
import Data.EGraph.EMatch.Types (Substitution (..))
import Data.EGraph.Immutable
import Data.EGraph.Saturation qualified as Sat
import Data.EGraph.Types.EGraph qualified as MEG
import Data.EGraph.Types.EGraph qualified as Raw
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Foldable (for_)
import Data.Foldable qualified as Fold
import Data.HashMap.Strict qualified as HMS
import Data.HashSet qualified as HSet
import Data.Hashable (Hashable)
import Data.IntMap.Strict qualified as IM
import Data.List (foldl')
import Data.Maybe (mapMaybe)
import GHC.Generics hiding ((:*:))
import Generics.Linear.TH qualified as LG
import Prelude.Linear (Consumable (..), Dupable, Movable, Ur (..))
import Prelude.Linear qualified as PL
import Test.Falsify.Generator qualified as F
import Test.Falsify.Predicate ((.$))
import Test.Falsify.Predicate qualified as Pred
import Test.Falsify.Range qualified as F
import Test.Tasty
import Test.Tasty.Falsify (Property, testProperty)
import Test.Tasty.Falsify qualified as F
import Test.Tasty.HUnit
import Text.Show.Borrowed (AsCopyableShow (..), Display)
import Prelude hiding (lookup)

data Expr a = a :+ a | a :* a | Lit Int | Var String
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving anyclass (Hashable)

deriveLanguage ''Expr

var :: String -> Term Expr
var = wrapTerm . Var

instance Num (Term Expr) where
  (+) = fmap wrapTerm . (:+)
  (*) = fmap wrapTerm . (:*)
  fromInteger n = wrapTerm $ Lit (fromInteger n)
  negate _ = error "negate is not supported"
  abs _ = error "abs is not supported"
  signum _ = error "signum is not supported"

instance Num (Pattern Expr v) where
  (+) = fmap PNode . (:+)
  (*) = fmap PNode . (:*)
  fromInteger n = PNode $ Lit (fromInteger n)
  negate _ = error "negate is not supported"
  abs _ = error "abs is not supported"
  signum _ = error "signum is not supported"

graph1 :: EGraph () Expr
graph1 = empty

ringRules :: [Rule Expr d String]
ringRules =
  [ named "add-zero" $ a + 0 ==> a
  , named "+-comm" $ a + b ==> b + a
  , named "*-comm" $ a * b ==> b * a
  , named "+-assoc-l" $ a + (b + c) ==> (a + b) + c
  , named "*-assoc-l" $ a * (b * c) ==> (a * b) * c
  , named "distrib" $ a * (b + c) ==> a * b + a * c
  , named "mul-one" $ a * 1 ==> a
  , named "mul-zero" $ 0 * a ==> 0
  ]
  where
    pvar :: String -> Pattern Expr String
    pvar = Metavar

    a = pvar "a"
    b = pvar "b"
    c = pvar "c"

test_saturate :: TestTree
test_saturate =
  testGroup
    "saturate"
    [ testCaseSteps "(a + b) * c == c * b + a * c" \step -> do
        step "Checking term polution..."
        let lhs = (a + b) * c
            rhs = c * b + a * c
        lookupTerm lhs graph1 @?= Nothing
        lookupTerm rhs graph1 @?= Nothing
        step "Adding terms..."
        let Ur graph =
              modify
                ( \eg -> Control.do
                    (Ur _, Ur _, eg) <- MEG.addTerm lhs eg
                    (Ur _, Ur _, eg) <- MEG.addTerm rhs eg
                    Control.pure (consume eg)
                )
                graph1
            lid = lookupTerm lhs graph
            rid = lookupTerm rhs graph
        case (lid, rid) of
          (Nothing, Nothing) -> assertFailure "Terms not found"
          (Just _, Nothing) -> assertFailure "RHS term not found"
          (Nothing, Just _) -> assertFailure "LHS term not found"
          (Just l, Just r) -> do
            step "Checking (non-)equivalence before saturation..."
            equivalent graph l r @?= Just False
            step "Saturating..."
            let !result = saturate defaultConfig ringRules graph
            step "Checking equivalence after saturation"
            case result of
              Left err -> assertFailure $ "saturation failed: " <> show err
              Right graph' -> equivalent graph' l r @?= Just True
    , testCaseSteps "(a + 0 + b) * c == c * b + a * c" \step -> do
        step "Checking term polution..."
        let lhs = ((a + 0 + b) * c)
            rhs = (c * b + a * c)
            lid = lookupTerm lhs graph1
            rid = lookupTerm rhs graph1
        lid @?= Nothing
        rid @?= Nothing
        step "Adding terms..."
        let Ur graph =
              modify
                ( \eg -> Control.do
                    (Ur _, Ur _, eg) <- MEG.addTerm lhs eg
                    Control.pure (consume eg)
                )
                graph1
            lid = lookupTerm lhs graph
            rid = lookupTerm rhs graph
        case (lid, rid) of
          (Nothing, Nothing) -> assertFailure "Terms not found"
          (_, Just _) -> assertFailure "RHS term should not be registered, but found!"
          (Just l, Nothing) -> do
            step "Saturating..."
            let !result = saturate defaultConfig {maxIterations = Just 5} ringRules graph
            step "Checking equivalence after saturation"
            case result of
              Left err -> assertFailure $ "saturation failed: " <> show err
              Right graph' -> do
                let rid = lookupTerm rhs graph'
                case rid of
                  Nothing -> assertFailure "RHS term not found after saturation"
                  Just r -> equivalent graph' l r @?= Just True
    , testCase "saturateFromList constructs and saturates in one lifetime" do
        let lhs = (a + b) * c
            rhs = c * b + a * c
            result :: Either (SaturationError Expr String) (EGraph () Expr, [EClassId])
            result = saturateFromList defaultConfig ringRules [lhs, rhs]
        case result of
          Left err -> assertFailure $ "saturation failed: " <> show err
          Right (graph, [lid, rid]) -> equivalent graph lid rid @?= Just True
          Right (_, ids) -> assertFailure $ "expected two input class ids, got: " <> show ids
    ]
  where
    a = var "a"
    b = var "b"
    c = var "c"

newtype ConstantFolding = ConstantFolding {constant :: Maybe Int}
  deriving (Eq, Show, Generic)

LG.deriveGeneric ''ConstantFolding

deriving via Generically ConstantFolding instance Copyable ConstantFolding

deriving via AsCopyable ConstantFolding instance Clone ConstantFolding

deriving via Generically ConstantFolding instance Consumable ConstantFolding

deriving via Generically ConstantFolding instance Dupable ConstantFolding

deriving via Generically ConstantFolding instance Movable ConstantFolding

deriving via
  AsCopyableShow ConstantFolding
  instance
    Display ConstantFolding

instance Semilattice ConstantFolding where
  ConstantFolding Nothing /\ ConstantFolding c = ConstantFolding c
  ConstantFolding c /\ ConstantFolding Nothing = ConstantFolding c
  ConstantFolding (Just x) /\ ConstantFolding (Just y)
    | x == y = ConstantFolding (Just x)
    | otherwise = ConstantFolding Nothing

instance Analysis Expr ConstantFolding where
  makeAnalysis (Lit n) = ConstantFolding (Just n)
  makeAnalysis Var {} = ConstantFolding Nothing
  makeAnalysis ((_, ConstantFolding l) :+ (_, ConstantFolding r)) =
    ConstantFolding $ (+) <$> l <*> r
  makeAnalysis ((_, ConstantFolding l) :* (_, ConstantFolding r)) =
    ConstantFolding $ (*) <$> l <*> r

  modifyAnalysis constFoldL eid egraph = Control.do
    (Ur anal, egraph) <- Raw.getAnalysis eid <$~ egraph
    case constant . view constFoldL =<< anal of
      Nothing -> Control.pure (consume egraph)
      Just v -> Control.do
        (Ur _, Ur eid', egraph) <- Raw.addTerm (wrapTerm $ Lit v) egraph
        if eid == eid'
          then Control.do
            Control.pure (consume egraph)
          else Control.do
            Control.void (Raw.unsafeMerge eid eid' egraph)

graphConstFold :: EGraph ConstantFolding Expr
graphConstFold = empty

test_constantFolding :: TestTree
test_constantFolding =
  testGroup
    "saturation with constant folding"
    [ checkFolding "1 + 1 == 2" (1 + 1) 2
    , checkFolding "(a + 2) * 5 == 10 + 5 * a" ((var "a" + 2) * 5) (10 + 5 * var "a")
    ]

checkFolding :: String -> Term Expr -> Term Expr -> TestTree
checkFolding name lhs rhs = testCase name do
  let graph = fromList @ConstantFolding [lhs]
  !graph' <- either throwIO pure $ saturate defaultConfig ringRules graph
  let eqv = equivalent graph' lhs rhs
  assertBool ("Expected to be equal, but got: " <> show eqv) (eqv == Just True)

newtype NodeCount = NodeCount Word
  deriving (Eq, Ord, Generic)
  deriving newtype (Show, Num, Copyable, Movable, Consumable, Dupable)

instance (Foldable f) => CostModel NodeCount f where
  costFunction = (+ 1) . sum

newtype Depth = Depth Word
  deriving (Eq, Ord, Generic)
  deriving newtype (Show, Num, Copyable, Movable, Consumable, Dupable)

instance (Foldable f) => CostModel Depth f where
  costFunction f = if null f then 0 else 1 + maximum f

test_extractBest :: TestTree
test_extractBest =
  testGroup
    "extractBest"
    [ testCase "a + 2 with a = 5 gives best term 7" do
        let term = var "a" + 2 :: Term Expr
            five = 5 :: Term Expr
            graph = fromList @(ExtractBest Expr NodeCount, ConstantFolding) [term, five]

        eid <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm term graph
        aId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm (var "a") graph
        fiveId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm five graph
        (bestTerm, count) <-
          maybe (assertFailure "term not found in initial graph") pure $
            extractBest eid graph
        count @?= 3
        bestTerm @?= term
        !graph' <-
          either throwIO pure $
            saturate defaultConfig ringRules $
              PL.unur PL.$
                modify
                  (Control.void PL.. Raw.merge aId fiveId)
                  graph

        (bestTerm, count) <-
          maybe (assertFailure "term not found in merged graph") pure $
            extractBest eid graph'
        count @?= 1
        bestTerm @?= 7
    , testCase "post-hoc extractBestWith agrees with maintained extractBest on cost" do
        -- Post-hoc extraction (reference semantics: egg's Extractor, hegg's
        -- findCosts) is ground truth; only the winning COST is compared in
        -- general, since tie-broken witness terms may differ by construction.
        let term = var "a" + 2 :: Term Expr
            five = 5 :: Term Expr
            graph = fromList @(ExtractBest Expr NodeCount, ConstantFolding) [term, five]

        eid <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm term graph
        aId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm (var "a") graph
        fiveId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm five graph

        (mTerm0, mCost0) <-
          maybe (assertFailure "maintained extractor found nothing") pure $
            extractBest eid graph
        (pTerm0, pCost0) <-
          maybe (assertFailure "post-hoc extractor found nothing") pure $
            extractBestWith @NodeCount eid graph
        pCost0 @?= mCost0
        -- tie-free class: the witness must agree, too
        pTerm0 @?= mTerm0

        !graph' <-
          either throwIO pure $
            saturate defaultConfig ringRules $
              PL.unur PL.$
                modify
                  (Control.void PL.. Raw.merge aId fiveId)
                  graph

        (_, mCost1) <-
          maybe (assertFailure "maintained extractor found nothing after merge") pure $
            extractBest eid graph'
        (pTerm1, pCost1) <-
          maybe (assertFailure "post-hoc extractor found nothing after merge") pure $
            extractBestWith @NodeCount eid graph'
        pCost1 @?= mCost1
        pTerm1 @?= 7
    , testCase "class node sets are canonical after saturation" do
        -- Guard for rebuild's canonical trim (egg's rebuild_classes): after a
        -- rebuild fixpoint, every node stored in a class set must be a
        -- fixpoint of canonicalization; database builds rely on this to skip
        -- per-row re-canonicalization.
        let term = var "a" + 2 :: Term Expr
            five = 5 :: Term Expr
            graph = fromList @(ExtractBest Expr NodeCount, ConstantFolding) [term, five]

        eid <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm term graph
        aId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm (var "a") graph
        fiveId <- maybe (assertFailure "term not found in initial graph") pure $ lookupTerm five graph

        !graph' <-
          either throwIO pure $
            saturate defaultConfig ringRules $
              PL.unur PL.$
                modify
                  (Control.void PL.. Raw.merge aId fiveId)
                  graph

        for_ [eid, aId, fiveId] \cid0 -> do
          cid <- maybe (assertFailure "find failed on saturated graph") pure $ find cid0 graph'
          ns <- maybe (assertFailure "class disappeared") pure $ lookupEClass cid graph'
          for_ ns \n ->
            canonicalize n graph' @?= Just n
    ]

{- | Random-graph property: post-hoc extraction ("Data.EGraph.Extraction",
the egg\/hegg reference pipeline) and the incrementally maintained
ExtractBest analysis must agree on the winning COST for every root
(witness terms may differ on exact-cost ties by construction).
Post-hoc is ground truth: a failure here is an ExtractBest-staleness
finding, not grounds to adjust the post-hoc extractor.
-}
test_extractEquivalenceProperty :: TestTree
test_extractEquivalenceProperty =
  testProperty "post-hoc extraction cost == maintained (random graphs)" do
    terms <- F.gen $ F.list (F.between (1, 5)) exprG
    i <- F.gen $ F.inRange (F.between (0, 31))
    j <- F.gen $ F.inRange (F.between (0, 31))
    checkExtractEquiv terms (i, j)

exprG :: F.Gen (Term Expr)
exprG = go (3 :: Int)
  where
    leaves = [var "a", var "b", var "c", 0, 1, 2]
    leafG = do
      i <- F.inRange (F.between (0, length leaves - 1))
      pure (leaves !! i)
    go n
      | n <= 0 = leafG
      | otherwise = do
          k <- F.inRange (F.between (0 :: Int, 3))
          case k of
            0 -> (+) <$> go (n - 1) <*> go (n - 1)
            1 -> (*) <$> go (n - 1) <*> go (n - 1)
            _ -> leafG

checkExtractEquiv :: [Term Expr] -> (Int, Int) -> Property ()
checkExtractEquiv terms (i, j) = do
  let graph0 = fromList @(ExtractBest Expr NodeCount, ConstantFolding) terms
      roots0 = mapMaybe (`lookupTerm` graph0) terms
      n = length roots0
      graph1
        | n == 0 = graph0
        | otherwise =
            let a = roots0 !! (i `mod` n)
                b = roots0 !! (j `mod` n)
             in PL.unur PL.$ modify (Control.void PL.. Raw.merge a b) graph0
  case saturate defaultConfig ringRules graph1 of
    Left err -> F.testFailed ("saturation failed: " <> show err)
    Right g ->
      mapM_
        ( \r -> do
            let mc = fmap snd (extractBest r g)
                pc = fmap snd (extractBestWith @NodeCount r g)
            -- Post-hoc is ground truth; the maintained analysis must agree
            -- on the winning cost (the pair-dedup analysis worklist fix —
            -- egg's UniqueQueue (node, class) semantics — repaired the
            -- staleness this property originally found).
            F.assert (Pred.eq .$ ("maintained", mc) .$ ("post-hoc", pc))
        )
        roots0

-- | B12 pin: compileRule reports the FULL dangling-variable set at once.
test_danglingPin :: TestTree
test_danglingPin = testCase "B12 pin: compileRule reports the full dangling set" do
  let bad = named "bad" (Metavar "a" ==> Metavar "b" + Metavar "c") :: Rule Expr () String
  case Sat.compileRule bad of
    Left (DanglingVariables vs) -> vs @?= HSet.fromList ["b", "c"]
    Right _ -> assertFailure "expected DanglingVariables"

{- | B12 pin: a side condition observes EXACTLY the named-variable map (no
extra keys, no missing keys), and a False condition gates the rewrite.
-}
test_sideConditionPin :: TestTree
test_sideConditionPin = testCase "B12 pin: side-condition map content and gating" do
  let lhsT = var "a" + var "b" :: Term Expr
      pa = Metavar "a"
      pb = Metavar "b"
      contentOk m = HMS.keysSet m == HSet.fromList ["a", "b"]
      goodRule = named "pin-good" ((pa + pb ==> pb * pa) Sat.@? contentOk)
      badRule = named "pin-block" ((pa + pb ==> pa * pb) Sat.@? const False)
  case saturateFromList defaultConfig {maxIterations = Just 2} [goodRule] [lhsT] ::
         Either (SaturationError Expr String) (EGraph () Expr, [EClassId]) of
    Left err -> assertFailure (show err)
    Right (g, [rid]) -> do
      swapped <-
        maybe (assertFailure "b*a not created - condition map content drifted") pure $
          lookupTerm (var "b" * var "a") g
      equivalent g rid swapped @?= Just True
    Right _ -> assertFailure "unexpected root ids"
  case saturateFromList defaultConfig {maxIterations = Just 2} [badRule] [lhsT] ::
         Either (SaturationError Expr String) (EGraph () Expr, [EClassId]) of
    Left err -> assertFailure (show err)
    Right (g, _) -> lookupTerm (var "a" * var "b") g @?= Nothing

{- | Verbatim pre-B12 reference: named-key ematch pipeline — per-match named
'Substitution' build (ascending-index insertion, vector-free fold) and dedup
hashing the (rootId, named) pair. Ground truth for the differential property.
-}
oldEmatchRef ::
  Q.PatternQuery Expr String ->
  Database Expr ->
  ([(EClassId, Substitution String)], Int)
oldEmatchRef Q.PatternQuery {..} db =
  ( nubRef HSet.empty $
      map
        ( \sub ->
            let !rootId = IM.findWithDefault (error "oldEmatchRef: root unbound") root sub
                !subs' =
                  Substitution $
                    foldl'
                      ( \acc (i, mname) -> case mname of
                          Just name | Just eid <- IM.lookup i sub -> HMS.insert name eid acc
                          _ -> acc
                      )
                      HMS.empty
                      (zip [0 ..] (Fold.toList varNames))
             in (rootId, subs')
        )
        subs
  , sum (IM.size <$> subs)
  )
  where
    subs = Rel.query patQuery db
    nubRef !_ [] = []
    nubRef !seen (m : rest)
      | HSet.member m seen = nubRef seen rest
      | otherwise = m : nubRef (HSet.insert m seen) rest

{- | B12 differential: the interned pipeline is observationally identical to
the pre-B12 named-key implementation — match list (order included), named
materialization, and the raw scheduler statistic — on random graphs with
merges and a rebuilt (canonical) database.
-}
test_ematchDifferential :: TestTree
test_ematchDifferential = testProperty "B12 differential: interned ematch == named reference" do
  terms <- F.gen $ F.list (F.between (1, 4)) exprG
  i <- F.gen $ F.inRange (F.between (0, 15))
  j <- F.gen $ F.inRange (F.between (0, 15))
  patIx <- F.gen $ F.inRange (F.between (0 :: Int, 3))
  let pat = case patIx of
        0 -> Metavar "x" + 0
        1 -> Metavar "x" + Metavar "x"
        2 -> Metavar "x"
        _ -> Metavar "x" + Metavar "y"
      graph0 = fromList @() terms
      roots0 = mapMaybe (`lookupTerm` graph0) terms
      n = length roots0
      graph1
        | n == 0 = graph0
        | otherwise =
            let a = roots0 !! (i `mod` n)
                b = roots0 !! (j `mod` n)
             in PL.unur PL.$
                  modify
                    ( \eg -> Control.do
                        (Ur _, eg) <- Raw.merge a b eg
                        eg <- Raw.rebuild eg
                        Control.pure (consume eg)
                    )
                    graph0
      db = buildDatabase graph1
      pq = Rel.compile pat :: Q.PatternQuery Expr String
      (refMatches, refRaw) = oldEmatchRef pq db
      (newInterned, newRaw) = Rel.ematchDbWithCount pq db
      newNamed = Rel.ematchDb pq db
  F.assert (Pred.eq .$ ("reference matches", refMatches) .$ ("interned pipeline", newNamed))
  F.assert (Pred.eq .$ ("reference rawSize", refRaw) .$ ("interned rawSize", newRaw))
  F.assert (Pred.eq .$ ("survivor count", length refMatches) .$ ("interned survivors", length newInterned))

{- | Deterministic reproducer for the falsify-found staleness: the maintained
'ExtractBest' analysis must agree with post-hoc extraction (ground truth) on
the winning cost.
-}
test_maintainedExtractFresh :: TestTree
test_maintainedExtractFresh = testCase "maintained ExtractBest equals post-hoc on the reproducer" do
  let aT = var "a"
      t = ((aT + aT) + (0 + aT)) * ((aT + aT) + (aT + aT))
      graph0 = fromList @(ExtractBest Expr NodeCount, ConstantFolding) [t]
  r <- maybe (assertFailure "root missing") pure $ lookupTerm t graph0
  g <- either (assertFailure . show) pure $ saturate defaultConfig ringRules graph0
  fmap snd (extractBest r g) @?= fmap snd (extractBestWith @NodeCount r g)
