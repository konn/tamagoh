{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}

module Data.HashMap.Linear.BorrowedSpec (
  module Data.HashMap.Linear.BorrowedSpec,
) where

import Data.HashMap.Linear.BorrowedCases
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_case1 :: TestTree
test_case1 = testCase "HashMap case 1" do
  let Ur HMCaseResult {..} = withNewHashMap case1
  residence @?= Nothing
  finalAnswer @?= Just 1
  finalEnts @?= [(1, 1)]

test_case2 :: TestTree
test_case2 = testCase "HashMap case 2" do
  let Ur HMCaseResult {..} = withNewHashMap case2
  residence @?= Nothing
  finalAnswer @?= Just 2
  finalEnts @?= [(2, 2)]
