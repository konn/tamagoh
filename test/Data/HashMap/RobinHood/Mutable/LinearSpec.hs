{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}

module Data.HashMap.RobinHood.Mutable.LinearSpec (
  module Data.HashMap.RobinHood.Mutable.LinearSpec,
) where

import Data.HashMap.RobinHood.Mutable.LinearSpec.Cases
import Prelude.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_case1 :: TestTree
test_case1 = testCase "HashMap case 1" do
  let Ur Case1Result {..} = withNewEmptyHashMap case1
  print Case1Result {..}
  initOneResident @?= Nothing
  newOneResident @?= Just 1
  initTwoResident @?= Nothing
  deltedOneResident @?= Just 1
  finalResult @?= [("Two", 2)]
