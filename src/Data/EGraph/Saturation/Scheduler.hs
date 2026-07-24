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
  banAtSearch,
  canStop,
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
  , deferOverLimitMatches :: !Bool
  {- ^ Enables egg's scheduler semantics: over-limit matches are /deferred/
  instead of applied. Default: 'False' (hegg's semantics).

  When 'False' (hegg's semantics), a rule that exceeds its threshold still
  has all of this iteration's matches applied; the ban only takes effect on
  later iterations, and saturation stops permanently at the first stalled
  iteration even while rules are banned.

  When 'True' (egg's semantics), an over-threshold rule is banned /before/
  application ('banAtSearch', egg's @BackoffScheduler::search_rewrite@): its
  matches are dropped for this iteration and the rule re-matches once the
  ban expires. Complementarily, a stalled iteration consults 'canStop'
  (egg's @BackoffScheduler::can_stop@): while any rule is banned, bans are
  shifted so the earliest expires immediately and saturation continues, so
  deferred work is eventually performed rather than lost. Matcher
  completeness is unaffected either way — scheduling only decides /when/
  matches are applied within a bounded run.
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
    , deferOverLimitMatches = False
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
                  -- hegg semantics: the ban duration doubles per PREVIOUS
                  -- ban count (first ban = banLength, then 2x, 4x, ...).
                  newBanDuration = banLength * (2 ^ prevTimesBanned)
                  newStat =
                    RuleStat
                      { bannedUntil = currentIter + newBanDuration
                      , timesBanned = newTimesBanned
                      }
               in IM.insert ruleIdx newStat s
            else s

{- | Search-time ban decision, faithful to egg's
@BackoffScheduler::search_rewrite@ (used when 'deferOverLimitMatches').

Given the number of substitutions a rule produced this iteration, decide
whether to ban it /now/: 'Just' returns the updated state and the caller must
drop this iteration's matches for the rule; 'Nothing' means the rule is under
its threshold and its matches may be applied. The threshold and ban duration
use the same exponential-backoff formulas as 'updateStats'.
-}
banAtSearch ::
  BackoffScheduler ->
  -- | Current iteration number
  Int ->
  -- | Rule index
  Int ->
  -- | Number of substitutions the rule matched this iteration
  Int ->
  -- | Current state
  SchedulerState ->
  Maybe SchedulerState
banAtSearch BackoffScheduler {..} currentIter ruleIdx matchCount state =
  let RuleStat {timesBanned = prevTimesBanned} =
        IM.findWithDefault (RuleStat 0 0) ruleIdx state
      threshold = matchLimit * (2 ^ prevTimesBanned)
   in if matchCount > threshold
        then
          Just $
            IM.insert
              ruleIdx
              RuleStat
                { bannedUntil = currentIter + banLength * (2 ^ prevTimesBanned)
                , timesBanned = prevTimesBanned + 1
                }
              state
        else Nothing

{- | Stall consultation, faithful to egg's @BackoffScheduler::can_stop@ (used
when 'deferOverLimitMatches').

'Nothing' means no rule is banned: the stall is a genuine fixpoint and
saturation may stop. @'Just' state'@ means some rules are still banned;
every ban has been shifted downward so the earliest expires immediately, and
the caller should run another iteration instead of stopping.
-}
canStop ::
  -- | Current iteration number
  Int ->
  -- | Current state
  SchedulerState ->
  Maybe SchedulerState
canStop currentIter state =
  let bannedVals = IM.filter (\rs -> bannedUntil rs > currentIter) state
   in if IM.null bannedVals
        then Nothing
        else
          let minBan = minimum (map bannedUntil (IM.elems bannedVals))
              delta = minBan - currentIter
              shift rs
                | bannedUntil rs > currentIter =
                    rs {bannedUntil = bannedUntil rs - delta}
                | otherwise = rs
           in Just (IM.map shift state)
