{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.RelationalSpec (
  module Data.EGraph.EMatch.RelationalSpec,
) where

import Data.EGraph.EMatch.RelationalCases
import Data.EGraph.TestUtils
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_case1 :: TestTree
test_case1 = testCase "simple relational ematch" do
  let n = 5
      Ur subss = withNewEGraph (mkCase1 n)
  length subss @?= n

test_nestedPin :: TestTree
test_nestedPin = testCase "B12 pin: nested two-atom pattern matches exactly once" do
  let Ur subss = withNewEGraph mkNestedPin
  length subss @?= 1

test_selectAllPin :: TestTree
test_selectAllPin = testCase "B12 pin: SelectAll dedups cross-operator multiplicity" do
  let Ur subss = withNewEGraph mkSelectAllPin
  -- classes after merging the I-class into the G-class: {I1,G} and the inner? —
  -- assert one match per class, no operator-multiplied duplicates
  length subss @?= length (foldr (\(cid, _) acc -> if cid `elem` acc then acc else cid : acc) [] subss)
