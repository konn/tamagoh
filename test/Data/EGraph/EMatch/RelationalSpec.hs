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
import Data.IntMap.Strict qualified as IM
import Data.List.NonEmpty qualified as NE
import Data.Trie qualified as Trie
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

test_preparedTransposePin :: TestTree
test_preparedTransposePin = testCase "T9 prepared transposition preserves exact matching" do
  preparedTransposePin
    @?= PreparedTransposePin
      { nestedOrderExact = True
      , nestedRawSizeExact = True
      , staticOrderExact = True
      , atomCountEligibilityExact = True
      , layoutValidationExact = True
      , repeatedVariableExact = True
      , fixedColumnFallbackExact = True
      , identityLayoutExact = True
      , missingRelationExact = True
      }

test_preparedDatabasePin :: TestTree
test_preparedDatabasePin = testCase "T9 fused prepared indexes preserve canonical matching" do
  let Ur result = withNewEGraph mkPreparedDatabasePin
  result
    @?= PreparedDatabasePin
      { fusedMatchesExact = True
      , preparedRowsExact = True
      , preparedOnlyCanonicalAbsent = True
      , preparedRequirementsExact = True
      , multipleLayoutsExact = True
      , absentPreparedFallbackExact = True
      }

test_mixedSelectAllSaturationPin :: TestTree
test_mixedSelectAllSaturationPin = testCase "T9 mixed SelectAll forces canonical prepared fallback" do
  let Ur result = withNewEGraph mkMixedSelectAllSaturationPin
  result @?= Just True

test_selectAllPin :: TestTree
test_selectAllPin = testCase "B12 pin: SelectAll dedups cross-operator multiplicity" do
  let Ur subss = withNewEGraph mkSelectAllPin
  -- classes after merging the I-class into the G-class: {I1,G} and the inner? —
  -- assert one match per class, no operator-multiplied duplicates
  length subss @?= length (foldr (\(cid, _) acc -> if cid `elem` acc then acc else cid : acc) [] subss)

test_databaseFilterCanonical :: TestTree
test_databaseFilterCanonical = testCase "operator filter agrees with full database after rebuild" do
  let Ur result = withNewEGraph (mkDatabaseFilterPin True)
  result @?= allDatabaseFilterChecks

test_databaseFilterNoncanonical :: TestTree
test_databaseFilterNoncanonical = testCase "operator filter agrees with full database after an unrepaired merge" do
  let Ur result = withNewEGraph (mkDatabaseFilterPin False)
  result @?= allDatabaseFilterChecks

allDatabaseFilterChecks :: DatabaseFilterPin
allDatabaseFilterChecks =
  DatabaseFilterPin
    { selectedLiteralEqual = True
    , selectedUnaryEqual = True
    , excludedLiteralEmpty = True
    , excludedBinaryEmpty = True
    , emptySelectionEmpty = True
    , auxiliaryIndexesEmpty = True
    , preparedMatchesEqual = True
    , preparedCanonicalizationEqual = True
    }

test_mixedSelectAll :: TestTree
test_mixedSelectAll = testCase "mixed SelectAll preserves exact multiplicity and scheduler counts" do
  let Ur result = withNewEGraph mkMixedSelectAllPin
  result
    @?= MixedSelectAllPin
      { selectAllOrderExact = True
      , selectAllMatchesExact = True
      , selectAllRawSizeExact = True
      , ordinaryMatchesExact = True
      , ordinaryRawSizeExact = True
      }

test_projectWithConstraints :: TestTree
test_projectWithConstraints = testCase "constrained projection agrees with focus then project" do
  let trie =
        Trie.fromRows
          [ [1, 10, 1, 100]
          , [1, 20, 1, 200]
          , [2, 10, 3, 100]
          , [3, 30, 3, 100]
          , [3, 30, 3, 100]
          ]
      check constraints positions =
        Trie.projectWithConstraints constraints positions trie
          @?= Trie.project
            positions
            (Trie.focus (NE.fromList (IM.toAscList constraints)) trie)
  check (IM.singleton 3 100) (0 NE.:| [2])
  check (IM.fromList [(0, 1), (3, 200)]) (1 NE.:| [])
  check (IM.fromList [(0, 3), (2, 3)]) (1 NE.:| [])
  check (IM.fromList [(0, 1), (3, 999)]) (1 NE.:| [])
