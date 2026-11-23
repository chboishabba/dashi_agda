module DASHI.Cognition.Teleodynamics.ScopedVerifierEvaluationProtocolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Product using (proj₁; proj₂)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL

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
    sameDeclaredConsumers : Bool
    sameValidatorScope : Bool
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

------------------------------------------------------------------------
-- ELIGIBLE-STRATUM WRAPPER
--
-- Empirical comparison is downstream of the existing repository eligibility
-- law.  A compact/cheap model cannot enter the ranked comparison merely by
-- passing a validator: both candidate and baseline must inhabit the SAME
-- ConsumerMDLProblem and carry MDL.Eligible receipts, i.e.
--
--   Admissible × ConsumerAdequate.
--
-- This wrapper does not alter the MDL calculus and does not manufacture either
-- obligation from observed benchmark performance.
------------------------------------------------------------------------

record EligibleEvaluationReceipt
    (problem : MDL.ConsumerMDLProblem) : Set₁ where
  constructor eligible-evaluation-receipt
  field
    evaluation : EvaluationReceipt
    candidateModel : MDL.Model problem
    baselineModel : MDL.Model problem
    candidateEligible : MDL.Eligible problem candidateModel
    baselineEligible : MDL.Eligible problem baselineModel
    candidateReferenceMatches :
      candidateLabel (pair evaluation) ≡
      MDL.modelReference problem candidateModel
    baselineReferenceMatches :
      baselineLabel (pair evaluation) ≡
      MDL.modelReference problem baselineModel
open EligibleEvaluationReceipt public

candidateAdmissibilityPaid :
  ∀ {problem} →
  (receipt : EligibleEvaluationReceipt problem) →
  MDL.Admissible problem (candidateModel receipt)
candidateAdmissibilityPaid receipt =
  proj₁ (candidateEligible receipt)

candidateConsumerAdequacyPaid :
  ∀ {problem} →
  (receipt : EligibleEvaluationReceipt problem) →
  MDL.ConsumerAdequate problem (candidateModel receipt)
candidateConsumerAdequacyPaid receipt =
  proj₂ (candidateEligible receipt)

baselineAdmissibilityPaid :
  ∀ {problem} →
  (receipt : EligibleEvaluationReceipt problem) →
  MDL.Admissible problem (baselineModel receipt)
baselineAdmissibilityPaid receipt =
  proj₁ (baselineEligible receipt)

baselineConsumerAdequacyPaid :
  ∀ {problem} →
  (receipt : EligibleEvaluationReceipt problem) →
  MDL.ConsumerAdequate problem (baselineModel receipt)
baselineConsumerAdequacyPaid receipt =
  proj₂ (baselineEligible receipt)

record EvaluationBoundary : Set where
  constructor evaluation-boundary
  field
    architectureImpliesEmpiricalWin : Bool
    zeroTrialCountAcceptedAsPerformance : Bool
    unmatchedBaselineAccepted : Bool
    consumerMismatchAccepted : Bool
    validatorScopeMismatchAccepted : Bool
    eligibleStratumRequiredBeforeComparison : Bool
    consumerInadequateModelAcceptedForComparison : Bool
    coverageSeparatedFromAccuracy : Bool
    abstentionSeparatedFromRefutation : Bool
    runtimeCostReportedSeparately : Bool

canonicalEvaluationBoundary : EvaluationBoundary
canonicalEvaluationBoundary =
  evaluation-boundary
    false false false false false true false true true true
