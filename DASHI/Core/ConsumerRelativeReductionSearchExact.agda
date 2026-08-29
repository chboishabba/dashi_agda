module DASHI.Core.ConsumerRelativeReductionSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as Canonical
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as FutureBridge
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- PURPOSE
--
-- Generic proof-search layer for model reduction.
--
-- The repo repeatedly uses the pattern
--
--   cheap candidate -> test declared consumer -> counterexample or certificate
--                   -> defer/reopen or escalate
--
-- This owner keeps candidate proposal, exact certification, counterexample
-- refutation, computational cost/order and hypothesis status separately typed.
-- It is repository-native and introduces no external scientific source claim.
------------------------------------------------------------------------

record ReductionCandidate
    (Fine Action Observation : Set)
    (fineStep : Action → Fine → Fine)
    (observe : Fine → Observation) : Set₁ where
  constructor reductionCandidate
  field
    Code : Set
    project : Fine → Code
    candidateLabel : String
    costRank : Nat
    fidelityReference : String
    assumptionReference : String
    applicationScopeReference : String

open ReductionCandidate public

------------------------------------------------------------------------
-- A certification fills exactly the data required to turn the proposed code
-- into the generic ConsumerRelativeReduction theorem owner.
------------------------------------------------------------------------

record CandidateCertification
    {Fine Action Observation : Set}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    (candidate : ReductionCandidate Fine Action Observation fineStep observe) : Set₁ where
  constructor candidateCertification
  field
    reducedStep : Action → Code candidate → Code candidate
    reducedObserve : Code candidate → Observation
    stepCommutes :
      (action : Action) (state : Fine) →
      project candidate (fineStep action state)
      ≡ reducedStep action (project candidate state)
    observationFactors :
      (state : Fine) →
      observe state ≡ reducedObserve (project candidate state)
    certificationReference : String
    validationScopeReference : String

open CandidateCertification public

certificationAsReduction :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : ReductionCandidate Fine Action Observation fineStep observe} →
  CandidateCertification candidate →
  Reduction.ConsumerRelativeReduction Fine Action Observation
certificationAsReduction {fineStep = fineStep} {observe = observe}
    {candidate = candidate} certificate =
  Reduction.consumerRelativeReduction
    (Code candidate)
    (project candidate)
    fineStep
    (reducedStep certificate)
    observe
    (reducedObserve certificate)
    (stepCommutes certificate)
    (observationFactors certificate)

CandidateRefutation :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation} →
  ReductionCandidate Fine Action Observation fineStep observe → Set
CandidateRefutation {fineStep = fineStep} {observe = observe} candidate =
  Reduction.CandidateReductionFailure fineStep observe (project candidate)

certifiedCandidateCanonicalFutureSafe :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : ReductionCandidate Fine Action Observation fineStep observe} →
  (certificate : CandidateCertification candidate) →
  (actionLabel : Action → String) →
  Future.FutureLanguageSafeProjection
    (FutureBridge.deterministicSystem fineStep actionLabel)
    observe
    (project candidate)
certifiedCandidateCanonicalFutureSafe certificate actionLabel =
  Canonical.canonicalFutureSafety
    (certificationAsReduction certificate)
    actionLabel

certificationExcludesCounterexample :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : ReductionCandidate Fine Action Observation fineStep observe} →
  CandidateCertification candidate →
  (actionLabel : Action → String) →
  CandidateRefutation candidate →
  ⊥
certificationExcludesCounterexample certificate actionLabel failure =
  Canonical.candidateFailureContradictsCanonicalFutureSafety
    actionLabel failure
    (certifiedCandidateCanonicalFutureSafe certificate actionLabel)

------------------------------------------------------------------------
-- Reopenable hypothesis semantics.
--
-- Refutation is an actual future-separating collision.  Dormant/deferred model
-- candidates can be reopened by an application-supplied evidence reference;
-- the generic forest therefore blocks pruning/deferment from becoming falsity.
------------------------------------------------------------------------

reductionHypothesisSemantics :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation} →
  Forest.HypothesisSemantics
    (ReductionCandidate Fine Action Observation fineStep observe)
reductionHypothesisSemantics =
  Forest.hypothesisSemantics
    CandidateRefutation
    (λ reason candidate → String)

noDeferredCandidateAutoRefutation :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : ReductionCandidate Fine Action Observation fineStep observe}
    {reason : Forest.DormancyReason} →
  Forest.HypothesisTransition
    reductionHypothesisSemantics
    candidate
    (Forest.reopenable reason)
    Forest.refuted →
  ⊥
noDeferredCandidateAutoRefutation = Forest.noDirectDormantRefutation

activeCandidateEntry :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation} →
  (candidate : ReductionCandidate Fine Action Observation fineStep observe) →
  Forest.HypothesisEntry
    (ReductionCandidate Fine Action Observation fineStep observe)
    Nat
activeCandidateEntry candidate =
  Forest.hypothesisEntry candidate Forest.active (costRank candidate)

refutedCandidateEntry :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation} →
  (candidate : ReductionCandidate Fine Action Observation fineStep observe) →
  CandidateRefutation candidate →
  Forest.HypothesisEntry
    (ReductionCandidate Fine Action Observation fineStep observe)
    Nat
refutedCandidateEntry candidate refutation =
  Forest.hypothesisEntry candidate Forest.refuted (costRank candidate)

------------------------------------------------------------------------
-- Proof-bearing escalation edge.  Cost need not be scalar in every domain;
-- this Nat rank is only the declared finite search order for this candidate
-- family, not a scientific quality score.
------------------------------------------------------------------------

record ReductionEscalationEdge
    {Fine Action Observation : Set}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    (from to : ReductionCandidate Fine Action Observation fineStep observe) : Set where
  constructor reductionEscalationEdge
  field
    fromCounterexample : CandidateRefutation from
    nondecreasingDeclaredCost : costRank from ≤ costRank to
    retainedCounterexampleReference : String
    escalationReasonReference : String

open ReductionEscalationEdge public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ReductionSearchBoundary : Set where
  constructor reductionSearchBoundary
  field
    cheapCandidateFailureNeedsFutureCounterexample : Bool
    deferredCandidateIsNotRefuted : Bool
    exactCertificateImpliesCanonicalFutureSafety : Bool
    exactCertificateCannotCoexistWithCounterexample : Bool
    higherCostImpliesGreaterScientificTruth : Bool
    higherCostImpliesGreaterScientificTruthIsFalse :
      higherCostImpliesGreaterScientificTruth ≡ false
    candidateCountOrRankCreatesSymmetry : Bool
    candidateCountOrRankCreatesSymmetryIsFalse :
      candidateCountOrRankCreatesSymmetry ≡ false

canonicalReductionSearchBoundary : ReductionSearchBoundary
canonicalReductionSearchBoundary =
  reductionSearchBoundary true true true true false refl false refl
