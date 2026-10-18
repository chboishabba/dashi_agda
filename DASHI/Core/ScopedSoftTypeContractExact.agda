module DASHI.Core.ScopedSoftTypeContractExact where

-- Context-indexed soft-typing/cardinality seam.
-- The existence of two differently named candidate values alone does not
-- certify a consumer-specific violation. Scope equality, applicability,
-- identity of the intended subject and value distinctness are hypotheses
-- supplied as proof-relevant inputs, not guessed by this module.
-- This is a DASHI extension of ContextIndexedPNFComparisonTransportExact.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
import DASHI.Core.ContextIndexedPNFComparisonTransportExact as Base

_≢_ : ∀ {X : Set} → X → X → Set
x ≢ y = x ≡ y → ⊥

record ScopedIncidence (Value : Set) : Set where
  constructor scoped-incidence
  field
    sourceRevisionRef : String
    nativeStatementRef : String
    subjectRef : String
    propertyRef : String
    scopeRef : String
    observedValue : Value
    applicabilityWitnessRef : String
open ScopedIncidence public

-- The consumer contract is NOT an assertion of globally extensional type
-- equality, and its scope need not be all times, places or source revisions.
record SingleValueDemand : Set where
  constructor single-value-demand
  field
    consumerRef : String
    contractRef : String
    scopedSubjectRef : String
    scopedPropertyRef : String
    requiredScopeRef : String
    originalContractSourceRef : String
open SingleValueDemand public

-- A counterexample requires *all* independently verified proof coordinates.
-- Unlike a Boolean mismatch, the type cannot be constructed from a missing
-- scope or applicability equality. The source locator strings are receipts,
-- not themselves a semantic proof.
record SingleValueCounterexample {Value : Set}
  (d : SingleValueDemand)
  (first second : ScopedIncidence Value) : Set where
  constructor counterexample
  field
    firstSubject : subjectRef first ≡ scopedSubjectRef d
    secondSubject : subjectRef second ≡ scopedSubjectRef d
    firstProperty : propertyRef first ≡ scopedPropertyRef d
    secondProperty : propertyRef second ≡ scopedPropertyRef d
    firstScope : scopeRef first ≡ requiredScopeRef d
    secondScope : scopeRef second ≡ requiredScopeRef d
    valuesDistinct : observedValue first ≢ observedValue second
    subjectIdentityEvidenceRef : String
    scopeComparabilityEvidenceRef : String
    valueDistinctnessEvidenceRef : String

open SingleValueCounterexample public

data ScopedJudgment {Value : Set}
  (d : SingleValueDemand)
  (first second : ScopedIncidence Value) : Set where
  witnessedViolation :
    SingleValueCounterexample d first second →
    ScopedJudgment d first second
  missingPremises :
    List String → ScopedJudgment d first second
  outsideScope :
    String → ScopedJudgment d first second

-- Constructive "violation implies a real witness" theorem:
-- a violation constructor cannot arise from a missing-premise judgment.
violationCarriesCounterexample :
  ∀ {Value : Set} {d : SingleValueDemand}
    {first second : ScopedIncidence Value} →
  (w : SingleValueCounterexample d first second) →
  observedValue first ≢ observedValue second
violationCarriesCounterexample w = valuesDistinct w

missingCannotBeViolation :
  ∀ {Value : Set} {d : SingleValueDemand}
    {first second : ScopedIncidence Value} →
  (missing : List String)
  (w : SingleValueCounterexample d first second) →
  ScopedJudgment.missingPremises missing ≢
    ScopedJudgment.witnessedViolation w
missingCannotBeViolation missing w ()

scopeOfWitnessedValuesAgrees :
  ∀ {Value : Set} {d : SingleValueDemand}
    {first second : ScopedIncidence Value} →
  (w : SingleValueCounterexample d first second) →
  scopeRef first ≡ scopeRef second
scopeOfWitnessedValuesAgrees w =
  Base.transEq (firstScope w) (Base.symEq (secondScope w))

-- A repair needs both an independent decrease in specifically demanded
-- residual debt and observational preservation, not just a patch function.
record MeasuredConsumerRepair
    (State Observation : Set)
    (observe : State → Observation)
    (debt : State → Set) : Set₁ where
  constructor measured-repair
  field
    before : State
    after : State
    consumerObservationPreserved :
      observe after ≡ observe before
    beforeDebtWitness : debt before
    afterDebtElimination : debt after → ⊥
    beforeSourceReceiptRef : String
    afterSourceReceiptRef : String
    rerunEvidenceRef : String

open MeasuredConsumerRepair public

repairEliminatesThisResidual :
  ∀ {State Observation : Set}
    {observe : State → Observation} {debt : State → Set} →
  (repair : MeasuredConsumerRepair State Observation observe debt) →
  debt (after repair) → ⊥
repairEliminatesThisResidual repair = afterDebtElimination repair
