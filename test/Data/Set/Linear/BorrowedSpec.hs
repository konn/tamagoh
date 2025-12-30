{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Set.Linear.BorrowedSpec (module Data.Set.Linear.BorrowedSpec) where

import Data.Set.Linear.BorrowedCases
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_case1 :: TestTree
test_case1 = testCase "Set case 1" do
  let Ur SetCaseResult {..} = withNewSet case1
  finalAnswer @?= True
  finalEnts @?= [1]

test_case2 :: TestTree
test_case2 = testCase "Set case 2" do
  let Ur SetCaseResult {..} = withNewSet case2
  finalAnswer @?= True
  finalEnts @?= [2]

test_copy :: TestTree
test_copy = testCase "Set copy case" do
  let Ur SetDupResult {..} = withNewSet copyCase
  initOrig @?= []
  insertedOrig @?= [1]
  initDup @?= [1]
  twiceInsertedOrig @?= [1, 2]
  finalDup @?= [1]
