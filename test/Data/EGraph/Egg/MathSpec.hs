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
import Tamagoh.Bench.Math
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTestBecause)
import Test.Tasty.HUnit
import Test.Tasty.HUnit qualified as Tasty
import Prelude hiding (lookup)

simple :: SaturationConfig
simple = defaultConfig

test_Math :: TestTree
test_Math =
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
        graph <- either throwIO pure $ saturate simple {maxIterations = Just 8} rules $ fromList [lhs]
        equivalent graph lhs rhs @?= Just True
        numEClasses graph @?= 127
    , testCase "math_fail" do
        graph <-
          either throwIO pure $
            saturate simple mathRulesTamagoh $
              fromList [var "x" + var "y"]
        _eid <- maybe (assertFailure "x + y not found") pure $ lookupTerm (var "x" + var "y") graph
        let xDIVy = lookupTerm (var "x" / var "y") graph
        isNothing xDIVy Tasty.@? "x / y should not be found, but got: " <> show xDIVy
    , ignoreTestBecause "It takes too much time" $ testCase "math_simplify_root" do
        let x = var "x"
        let lhs = 1 / (((1 + sqrt x) / 2) - ((1 - sqrt x) / 2))
        !graph <-
          either throwIO pure $
            saturate simple {nodeLimit = Just 75_000, maxIterations = Just 9} mathRulesTamagoh $
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
            saturate simple mathRulesTamagoh $
              fromList [lhs]
        lid <- maybe (assertFailure "lhs not found") pure $ lookupTerm lhs graph
        rid <- maybe (assertFailure "rhs not found") pure $ lookupTerm rhs graph
        equivalent graph lid rid @?= Just True
    ]
