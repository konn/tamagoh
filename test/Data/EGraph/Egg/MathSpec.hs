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

module Data.EGraph.Egg.MathSpec (module Data.EGraph.Egg.MathSpec) where

import Control.Exception (throwIO)
import Data.EGraph.Immutable
import Data.Maybe (isNothing)
import Tamagoh.Bench.Math hiding (Rule, named, (==>), (@?))
import Tamagoh.Bench.Math qualified as Bench (BenchCost)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit qualified as Tasty
import Prelude hiding (lookup)

simple :: SaturationConfig
simple = defaultConfig

theRules :: [Rule Math ConstantFold String]
theRules = mathRulesTamagoh

-- | Analysis type that enables extraction
type ExtractAnalysis = (ExtractBest Math Bench.BenchCost, ConstantFold)

-- | Rules for extraction tests
extractRules :: [Rule Math ExtractAnalysis String]
extractRules = mathRulesTamagoh

test_Math :: TestTree
test_Math =
  adjustOption (const $ mkTimeout 90_000_000) $
    testGroup
      "Math tests from egraphs-good/egg"
      [ testCase "math_associate_adds" do
          let a = Metavar "a"
              b = Metavar "b"
              c = Metavar "c"
              rules :: [Rule Math () String]
              !rules =
                [ named "comm-add" $ a + b ==> b + a
                , named "assoc-add" $ (a + b) + c ==> a + (b + c)
                ]
              !lhs = foldr1 (+) $ map lit [1 .. 7] :: Term Math
              !rhs = foldr1 (+) $ map lit [7, 6 .. 1] :: Term Math
          graph <- either throwIO pure $ saturate simple {maxIterations = Just 8, scheduler = Nothing} rules $ fromList [lhs]
          equivalent graph lhs rhs @?= Just True
          numEClasses graph @?= 127
      , testCase "sub_canon_simple" do
          -- Test that sub-canon rule works: a - b ==> a + (-1 * b)
          let x = var "x"
              lhs = 0 - x
              expected = 0 + ((-1) * x) :: Term Math
              zeroMinusOne = sub (lit 0) (lit 1) :: Term Math
              subCanonRule :: [Rule Math ConstantFold String]
              subCanonRule = [named "sub-canon" $ Metavar "a" - Metavar "b" ==> Metavar "a" + ((-1) * Metavar "b")]
          !graph <-
            either throwIO pure $
              saturate simple {maxIterations = Just 5} subCanonRule $
                fromList [lhs, zeroMinusOne]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          case lookupTerm expected graph of
            Just eid -> do
              equivalent graph lid eid @?= Just True
            Nothing -> assertFailure "expected term not found"
      , testCase "d_variable_rule" do
          -- Test that diff(x, x) ==> 1 works (WITHOUT side condition)
          let x = var "x"
              lhs = diff x x
              rhs = 1 :: Term Math
              -- Rule without side condition first to test pattern matching
              dVarRule :: [Rule Math ConstantFold String]
              dVarRule = [named "d-variable" $ diff (Metavar "x") (Metavar "x") ==> 1]
          !graph <-
            either throwIO pure $
              saturate simple {maxIterations = Just 10} dVarRule $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCaseSteps "math_fail" \step -> do
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [var "x" + var "y"]
          step "Checking that x / y is not found"
          _eid <- maybe (assertFailure "x + y not found") pure $ lookupTerm (var "x" + var "y") graph
          let xDIVy = lookupTerm (var "x" / var "y") graph
          isNothing xDIVy Tasty.@? "x / y should not be found, but got: " <> show xDIVy
      , testCase "math_simplify_root" do
          let x = var "x"
          let lhs = 1 / (((1 + sqrt x) / 2) - ((1 - sqrt x) / 2))
          !graph <-
            either throwIO pure $
              saturate simple {nodeLimit = Just 75_000, maxIterations = Just 9} theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "1 / sqrt x not found") pure $ lookupTerm (1 / sqrt x) graph
          equivalent graph lid rid @?= Just True
      , testCase "math_simplify_factor" do
          let x = var "x"
              lhs = (x + 3) * (x + 1)
              rhs = ((x * x) + (4 * x)) + 3
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_simplify_add" do
          let x = var "x"
              lhs = x + (x + (x + x))
              rhs = 4 * x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_powers" do
          let x = var "x"
              y = var "y"
              lhs = (2 ** x) * (2 ** y)
              rhs = 2 ** (x + y)
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_simplify_const" do
          let a = var "a"
              lhs = 1 + (a - ((2 - 1) * a))
              rhs = 1 :: Term Math
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_diff_same" do
          let x = var "x"
              lhs = diff x x
              rhs = 1 :: Term Math
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_diff_different" do
          let x = var "x"
              y = var "y"
              lhs = diff x y
              rhs = 0 :: Term Math
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_diff_simple1" do
          let x = var "x"
              lhs = diff x (1 + (2 * x))
              rhs = 2 :: Term Math
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_diff_simple2" do
          let x = var "x"
              y = var "y"
              lhs = diff x (1 + (y * x))
              rhs = y
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "math_diff_ln" do
          let x = var "x"
              lhs = diff x (lnE x)
              rhs = 1 / x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "diff_power_simple" do
          let x = var "x"
              lhs = diff x (x ** 3)
              rhs = 3 * (x ** 2)
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "diff_power_harder" do
          let x = var "x"
              lhs = diff x ((x ** 3) - (7 * (x ** 2)))
              rhs = x * ((3 * x) - 14)
          !graph <-
            either throwIO pure $
              saturate simple {nodeLimit = Just 100_000, maxIterations = Just 60} theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "integ_one" do
          let x = var "x"
              lhs = integral 1 x
              rhs = x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "integ_sin" do
          let x = var "x"
              lhs = integral (cos x) x
              rhs = sin x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "integ_x" do
          let x = var "x"
              lhs = integral (x ** 1) x
              rhs = (x ** 2) / 2
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "integ_part1" do
          let x = var "x"
              lhs = integral (x * cos x) x
              rhs = (x * sin x) + cos x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      , testCase "integ_part2" do
          let x = var "x"
              lhs = integral (cos x * x) x
              expectedRhs = (x * sin x) + cos x
              -- No scheduler - need all rules to find simplification
              cfg = simple {nodeLimit = Just 50_000, maxIterations = Just 100, scheduler = Nothing}
          !graph <-
            either throwIO pure $
              saturate cfg extractRules $
                fromList @ExtractAnalysis [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          -- Extract the best term and compare to expected
          (extracted, _cost) <- maybe (assertFailure "extraction failed") pure $ extractBest lid graph
          -- The extracted term should equal the expected RHS
          extracted @?= expectedRhs
      , testCase "integ_part3" do
          let x = var "x"
              lhs = integral (lnE x) x
              rhs = (x * lnE x) - x
          !graph <-
            either throwIO pure $
              saturate simple theRules $
                fromList [lhs]
          lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
          rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
          equivalent graph lid rid @?= Just True
      ]
