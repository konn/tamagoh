{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
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
import Data.EGraph.Immutable
import Data.EGraph.Types.EGraph qualified as MEG
import Data.EGraph.Types.EGraph qualified as Raw
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Hashable (Hashable)
import GHC.Generics hiding ((:*:))
import Generics.Linear.TH qualified as LG
import Prelude.Linear (Consumable (..), Dupable, Movable, Ur (..))
import Prelude.Linear qualified as PL
import Test.Tasty
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

ringRules :: [Rule Expr String]
ringRules =
  [ named "add-zero" $ a + 0 ==> a
  , named "+-comm" $ a + b ==> b + a
  , named "*-comm" $ a * b ==> b * a
  , named "+-assoc-r" $ (a + b) + c ==> a + (b + c)
  , named "+-assoc-l" $ a + (b + c) ==> (a + b) + c
  , named "*-assoc-r" $ (a * b) * c ==> a * (b * c)
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
            let result = saturate SaturationConfig {maxIterations = Nothing} ringRules graph
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
            let result = saturate SaturationConfig {maxIterations = Nothing} ringRules graph
            step "Checking equivalence after saturation"
            case result of
              Left err -> assertFailure $ "saturation failed: " <> show err
              Right graph' -> do
                let rid = lookupTerm rhs graph'
                case rid of
                  Nothing -> assertFailure "RHS term not found after saturation"
                  Just r -> equivalent graph' l r @?= Just True
    ]
  where
    a = var "a"
    b = var "b"
    c = var "c"

newtype ConstantFolding = ConstantFolding {constant :: Maybe Int}
  deriving (Eq, Show, Generic)

LG.deriveGeneric ''ConstantFolding

deriving via Generically ConstantFolding instance Copyable ConstantFolding

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
    | otherwise =
        error $ "ConstantFolding: conflicting constants: " <> show (x, y)

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
  graph' <- either throwIO pure $ saturate SaturationConfig {maxIterations = Nothing} ringRules graph
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
        graph' <-
          either throwIO pure $
            saturate SaturationConfig {maxIterations = Nothing} ringRules $
              PL.unur PL.$
                modify
                  (Control.void PL.. Raw.merge aId fiveId)
                  graph

        (bestTerm, count) <-
          maybe (assertFailure "term not found in merged graph") pure $
            extractBest eid graph'
        count @?= 1
        bestTerm @?= 7
    ]
