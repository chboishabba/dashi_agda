module DASHI.Cognition.Teleodynamics.ScopedVerifierEvaluationProtocolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- Empirical protocol only: no scores are manufactured.  Every promotion from
-- architecture to comparative performance requires a same-task matched receipt.

record EvaluationTask : Set where
  constructor evaluation-task
  field
    taskLabel : String
    declaredDomain : String
    heldOutProtocol : String
open EvaluationTask public

record MatchedSystemPair : Set where
  constructor matched-system-pair
  field
    candidateLabel : String
    baselineLabel : String
    sameTaskSet : Bool
    sameToolAccess : Bool
    sameContextBudget : Bool
    sameComputeAccounting : Bool
open MatchedSystemPair public

record ComparativeMeasurements : Set where
  constructor comparative-measurements
  field
    editIdentityTrials : Nat
    editIdentitySuccesses : Nat
    factualTrials : Nat
    factualVerifiedCorrect : Nat
    oodTrials : Nat
    oodCorrectAbstentions : Nat
    applicableTrials : Nat
    validatorCoveredTrials : Nat
    candidateCostUnits : Nat
    baselineCostUnits : Nat
open ComparativeMeasurements public

record EvaluationReceipt : Set where
  constructor evaluation-receipt
  field
    task : EvaluationTask
    pair : MatchedSystemPair
    measurements : ComparativeMeasurements
    provenance : String
    independentlyReproducible : Bool
open EvaluationReceipt public

record EvaluationBoundary : Set where
  constructor evaluation-boundary
  field
    architectureImpliesEmpiricalWin : Bool
    zeroTrialCountAcceptedAsPerformance : Bool
    unmatchedBaselineAccepted : Bool
    coverageSeparatedFromAccuracy : Bool
    abstentionSeparatedFromRefutation : Bool
    runtimeCostReportedSeparately : Bool

canonicalEvaluationBoundary : EvaluationBoundary
canonicalEvaluationBoundary = evaluation-boundary false false false true true true
