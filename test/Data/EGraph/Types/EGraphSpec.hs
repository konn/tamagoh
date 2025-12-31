{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.EGraph.Types.EGraphSpec (
  module Data.EGraph.Types.EGraphSpec,
) where

import Data.EGraph.TestUtils
import Data.EGraph.Types.EGraphSpec.Cases
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit
import Prelude as P

-- NOTE: case 1 and 2 are almost identical -
-- but we had a case where two test cases are run in a row ir parallel,
-- at lsast one of them fails due to some unexpected shared state.
-- This error is falky and sometimes does not show up.

test_case1 :: TestTree
test_case1 = testCase "union a b" $ do
  let Ur MiniCaseResult {..} = withNewEGraph case1
  putStrLn $ "Case 1 result: " <> show MiniCaseResult {..}
  assertBool ("a /= b at first, but got: " <> show abEqAtFst) (abEqAtFst == Just False)
  assertBool ("a == b after merge, but got: " <> show abEqAtLast) (abEqAtLast == Just True)

test_case2 :: TestTree
test_case2 = testCase "union a 5" $ do
  let Ur MiniCaseResult {..} = withNewEGraph case2
  putStrLn $ "Case 2 result: " <> show MiniCaseResult {..}
  assertBool ("a /= 5 at first, but got: " <> show abEqAtFst) (abEqAtFst == Just False)
  assertBool ("a == 5 after merge, but got: " <> show abEqAtLast) (abEqAtLast == Just True)

test_case3 :: TestTree
test_case3 = testCase "a + b vs a + c" $ do
  let Ur Case1Result {..} = withNewEGraph case3
  assertBool ("(a + b) /= (a + c) at first, but got: " <> show abacEqAtFirst) (abacEqAtFirst == Just False)
  assertBool ("(a + b) == (a + c) after merge, but got: " <> show abacEqAfterMerge) (abacEqAfterMerge == Just True)

test_case4 :: TestTree
test_case4 = testCase "a + b vs a + 5" $ do
  let Ur Case1Result {..} = withNewEGraph case4
  assertBool ("(a + b) /= (a + 5) at first, but got: " <> show abacEqAtFirst) (abacEqAtFirst == Just False)
  assertBool ("(a + b) == (a + 5) after merge, but got: " <> show abacEqAfterMerge) (abacEqAfterMerge == Just True)
