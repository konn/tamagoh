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

import Control.Monad.Borrow.Pure (linearly)
import Data.EGraph.EMatch.RelationalCases
import Data.EGraph.TestUtils
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_case1 :: TestTree
test_case1 = testCase "simple relational ematch" do
  let n = 5
      Ur (Ur subss) = linearly do withNewEGraph (mkCase1 n)
  length subss @?= n
