module DASHI.Biology.Levin.GoalCompletionDriftAging where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.HierarchicalGoalMemory as Hierarchy
import DASHI.Biology.Levin.CompetentGoalExecution as Execution
import DASHI.Biology.Levin.FunctionalAgencyRatchet as Ratchet

------------------------------------------------------------------------
-- Candidate cybernetic aging mechanism after prolonged target satisfaction.

record GoalCompletionDriftModel : Set where
  field
    targetSpecified              : Bool
    rewardOrErrorSignalSpecified : Bool
    targetInitiallyReached       : Bool
    noInjectedDamageRequired     : Bool
    noProgrammedAgingRequired    : Bool
    postCompletionDriftObserved  : Bool
    challengeRestoresPerformance : Bool
    comparisonToNoiseModelMade   : Bool
    comparisonToProgramModelMade : Bool
    interpretation               : String

record GoalCompletionDriftBoundary : Set where
  field
    hierarchyLaneImported : Bool
    executionLaneImported : Bool
    agencyRatchetImported : Bool
    simulationNotBiologicalProof : Bool
    regenerationNotNecessaryForRejuvenation : Bool
    challengeNotUniversalTherapy : Bool
    cognitiveMeansCyberneticNotHumanPsychology : Bool
    damageAndProgramTheoriesRemainLive : Bool
    humanLongevityAuthorityBlocked : Bool

canonicalGoalCompletionDriftBoundary : GoalCompletionDriftBoundary
canonicalGoalCompletionDriftBoundary = record
  { hierarchyLaneImported = true
  ; executionLaneImported = true
  ; agencyRatchetImported = true
  ; simulationNotBiologicalProof = true
  ; regenerationNotNecessaryForRejuvenation = true
  ; challengeNotUniversalTherapy = true
  ; cognitiveMeansCyberneticNotHumanPsychology = true
  ; damageAndProgramTheoriesRemainLive = true
  ; humanLongevityAuthorityBlocked = true
  }
