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

import Control.Monad.Borrow.Pure
import Data.EGraph.Types.EGraphSpec.Cases
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit
import Prelude as P

test_case1 :: TestTree
test_case1 = testCase "EGraph case 1" $ do
  let Ur resl@Case1Result {..} = linearly (withNewEGraph case1)
  putStrLn $ "Result: " <> P.show resl
  assertBool ("(a + b) /= (a + c) at first, but got: " <> show abacEqAtFirst) (abacEqAtFirst == Just False)
  assertBool ("(a + b) == (a + c) after merge, but got: " <> show abacEqAfterMerge) (abacEqAfterMerge == Just True)
