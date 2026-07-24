{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}

module Data.SlotMap.Linear.BorrowedSpec (
  module Data.SlotMap.Linear.BorrowedSpec,
) where

import Data.SlotMap.Linear.BorrowedCases
import Data.Unrestricted.Linear (Ur (..))
import Test.Tasty
import Test.Tasty.HUnit

test_dense :: TestTree
test_dense = testCase "SlotMap dense push 0..99 (growth, ascending order)" do
  let Ur DenseResult {..} = withNewSlotMap caseDense
  allFresh @?= True
  liveCount @?= 100
  entries @?= [(i, i * 10) | i <- [0 .. 99]]

test_holes :: TestTree
test_holes = testCase "SlotMap deletion holes and hole re-insert" do
  let Ur HolesResult {..} = withNewSlotMap caseHoles
  afterDeletes @?= 5
  evenGone @?= True
  oddKept @?= True
  doubleDelete @?= Nothing
  refillFresh @?= Nothing
  finalCount @?= 6

test_ownedAndGrowth :: TestTree
test_ownedAndGrowth = testCase "SlotMap owned delete + borrow mutation across regrows" do
  let Ur (recovered, sz) = withNewSlotMap caseOwnedAndGrowth
  recovered @?= 42
  sz @?= 63

test_sparse :: TestTree
test_sparse = testCase "SlotMap sparse insert past the bound" do
  let Ur (freshAndMissing, sz, entries) = withNewSlotMap caseSparse
  freshAndMissing @?= True
  sz @?= 1
  entries @?= [(10, 1010)]
