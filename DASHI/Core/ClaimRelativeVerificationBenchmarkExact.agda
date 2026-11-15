module DASHI.Core.ClaimRelativeVerificationBenchmarkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ClaimRelativeVerificationEscalationExact as Verification

------------------------------------------------------------------------
-- PAIRED ACT / ABSTAIN BENCHMARK
--
-- A should-act task and its should-abstain counterpart share a declared base
-- environment and differ by an explicitly witnessed controlled perturbation.
-- The benchmark does not permit an always-act or always-abstain policy to be
-- relabelled as paired success.
------------------------------------------------------------------------

record PairedActionAbstentionCase
    (Environment Task : Set) : Set₁ where
  constructor paired-action-abstention-case
  field
    environment : Environment
    shouldActTask : Task
    shouldAbstainTask : Task
    ControlledPerturbation : Set
    controlledPerturbation : ControlledPerturbation
    criticalActionReference : String
    pairReference : String

open PairedActionAbstentionCase public


data ObservedActionDisposition : Set where
  acted : ObservedActionDisposition
  abstainedBeforeCriticalAction : ObservedActionDisposition
  abstainedAfterCriticalAction : ObservedActionDisposition
  failedWithoutDecision : ObservedActionDisposition

record PairedActionAbstentionResult
    {Environment Task : Set}
    (pair : PairedActionAbstentionCase Environment Task) : Set where
  constructor paired-action-abstention-result
  field
    shouldActObserved : ObservedActionDisposition
    shouldAbstainObserved : ObservedActionDisposition
    traceReference : String
    outcomeReference : String

open PairedActionAbstentionResult public

PairedCorrect :
  ∀ {Environment Task}
    {pair : PairedActionAbstentionCase Environment Task} →
  PairedActionAbstentionResult pair → Set
PairedCorrect result =
  (shouldActObserved result ≡ acted) ×
  (shouldAbstainObserved result ≡ abstainedBeforeCriticalAction)

------------------------------------------------------------------------
-- Weak/strong selective-verification scorecard.
-- Counts remain separate coordinates.  No scalar utility or optimal policy is
-- silently imported from external weak/strong-verification literature.
------------------------------------------------------------------------

record SelectiveVerificationScorecard : Set where
  constructor selective-verification-scorecard
  field
    trialCount : Nat
    incorrectAcceptanceCount : Nat
    incorrectRejectionCount : Nat
    strongVerificationCount : Nat
    abstentionCount : Nat
    outOfDomainCount : Nat
    validatorSuccessConsumerFailureCount : Nat
    runtimeCostReference : String
    calibrationReference : String
    scorecardReference : String

open SelectiveVerificationScorecard public

------------------------------------------------------------------------
-- Matched-comparator contract.  Matching is consumer-relative and includes
-- the resources that could otherwise make a nominal head-to-head comparison
-- incomparable.
------------------------------------------------------------------------

record MatchedComparatorContract : Set where
  constructor matched-comparator-contract
  field
    sameTaskSet : Set
    sameTaskSetReceipt : sameTaskSet
    sameToolAccess : Set
    sameToolAccessReceipt : sameToolAccess
    sameContextBudget : Set
    sameContextBudgetReceipt : sameContextBudget
    sameComputeAccounting : Set
    sameComputeAccountingReceipt : sameComputeAccounting
    sameDeclaredConsumer : Set
    sameDeclaredConsumerReceipt : sameDeclaredConsumer
    sameValidatorScope : Set
    sameValidatorScopeReceipt : sameValidatorScope
    comparatorReference : String

open MatchedComparatorContract public

------------------------------------------------------------------------
-- End-to-end benchmark packet.  It binds the generic claim-relative
-- evaluation packet to an explicit matched comparator and scorecard, and may
-- additionally include paired action/abstention trials.  No field manufactures
-- world truth or mechanism identity.
------------------------------------------------------------------------

record ClaimRelativeVerificationBenchmark
    (problem : MDL.ConsumerMDLProblem)
    (Source Specification Consumer : Set)
    (Object Intervention Repair Training HeldOut Prediction : Set)
    (ValidatorObservation ConsumerObservation : Set) : Set₁ where
  constructor claim-relative-verification-benchmark
  field
    evaluation :
      Verification.ClaimRelativeEvaluationPacket
        problem Source Specification Consumer
        Object Intervention Repair Training HeldOut Prediction
        ValidatorObservation ConsumerObservation
    comparator : MatchedComparatorContract
    scorecard : SelectiveVerificationScorecard
    benchmarkReference : String

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record ClaimRelativeVerificationBenchmarkBoundary : Set where
  constructor claim-relative-verification-benchmark-boundary
  field
    postHocAbstentionCountsAsSuccessfulAbstention : Bool
    postHocAbstentionCountsAsSuccessfulAbstentionIsFalse :
      postHocAbstentionCountsAsSuccessfulAbstention ≡ false

    abstentionEvaluationUsesPairedActAbstainCases : Bool
    abstentionEvaluationUsesPairedActAbstainCasesIsTrue :
      abstentionEvaluationUsesPairedActAbstainCases ≡ true

    singleAggregateScoreDeterminesReliability : Bool
    singleAggregateScoreDeterminesReliabilityIsFalse :
      singleAggregateScoreDeterminesReliability ≡ false

    comparatorMayChangeDeclaredConsumer : Bool
    comparatorMayChangeDeclaredConsumerIsFalse :
      comparatorMayChangeDeclaredConsumer ≡ false

    comparatorMayChangeValidatorScope : Bool
    comparatorMayChangeValidatorScopeIsFalse :
      comparatorMayChangeValidatorScope ≡ false

    validatorSuccessMaySubstituteForConsumerOutcome : Bool
    validatorSuccessMaySubstituteForConsumerOutcomeIsFalse :
      validatorSuccessMaySubstituteForConsumerOutcome ≡ false

    zeroTrialScorecardCountsAsEmpiricalSupport : Bool
    zeroTrialScorecardCountsAsEmpiricalSupportIsFalse :
      zeroTrialScorecardCountsAsEmpiricalSupport ≡ false

canonicalClaimRelativeVerificationBenchmarkBoundary :
  ClaimRelativeVerificationBenchmarkBoundary
canonicalClaimRelativeVerificationBenchmarkBoundary =
  claim-relative-verification-benchmark-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
