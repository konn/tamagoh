{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

{- | Backoff scheduler for equality saturation.

The backoff scheduler prevents explosive rule growth by temporarily banning
rules that produce too many matches. When a rule exceeds its match threshold,
it gets banned for a number of iterations. The ban duration doubles
exponentially each time the rule is banned.

This is based on the scheduler design from egg/hegg.
-}
module Data.EGraph.Saturation.Scheduler (
  -- * Scheduler Configuration
  BackoffScheduler (..),
  defaultScheduler,

  -- * Scheduler State
  SchedulerState,
  RuleStat (..),
  initialState,

  -- * Scheduler Operations
  isBanned,
  updateStats,
) where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import GHC.Generics (Generic)

-- | Configuration for the backoff scheduler.
data BackoffScheduler = BackoffScheduler
  { matchLimit :: !Int
  {- ^ Maximum number of matches before a rule gets banned.
  Default: 1000
  -}
  , banLength :: !Int
  {- ^ Base number of iterations a rule stays banned.
  The actual ban duration is @banLength * 2^timesBanned@.
  Default: 5
  -}
  }
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

{- | Default scheduler configuration.
Match limit is 5000, ban length is 2.
These values are calibrated to allow rules to explore sufficiently
while still preventing exponential explosion.
-}
defaultScheduler :: BackoffScheduler
defaultScheduler =
  BackoffScheduler
    { matchLimit = 1000
    , banLength = 10
    }

-- | Statistics for a single rule.
data RuleStat = RuleStat
  { bannedUntil :: !Int
  {- ^ Iteration number when the ban expires.
  The rule is banned while @currentIteration < bannedUntil@.
  -}
  , timesBanned :: !Int
  {- ^ Number of times this rule has been banned.
  Used to calculate exponential backoff.
  -}
  }
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

{- | Scheduler state tracking statistics for all rules.
Keys are rule indices (0-based).
-}
type SchedulerState = IntMap RuleStat

-- | Initial scheduler state with no rules banned.
initialState :: SchedulerState
initialState = IM.empty

-- | Check if a rule is currently banned.
isBanned ::
  -- | Current iteration number
  Int ->
  -- | Rule index
  Int ->
  -- | Scheduler state
  SchedulerState ->
  Bool
isBanned currentIter ruleIdx state =
  case IM.lookup ruleIdx state of
    Nothing -> False
    Just RuleStat {..} -> currentIter < bannedUntil

{- | Update scheduler state after matching.
If a rule produced more matches than its threshold, ban it.
-}
updateStats ::
  BackoffScheduler ->
  -- | Current iteration number
  Int ->
  -- | List of (rule index, match count) pairs
  [(Int, Int)] ->
  -- | Current state
  SchedulerState ->
  SchedulerState
updateStats BackoffScheduler {..} currentIter matchCounts state =
  foldr updateRule state matchCounts
  where
    updateRule (ruleIdx, matchCount) s =
      let RuleStat {timesBanned = prevTimesBanned} =
            IM.findWithDefault (RuleStat 0 0) ruleIdx s
          threshold = matchLimit * (2 ^ prevTimesBanned)
       in if matchCount > threshold
            then
              let newTimesBanned = prevTimesBanned + 1
                  newBanDuration = banLength * (2 ^ newTimesBanned)
                  newStat =
                    RuleStat
                      { bannedUntil = currentIter + newBanDuration
                      , timesBanned = newTimesBanned
                      }
               in IM.insert ruleIdx newStat s
            else s
