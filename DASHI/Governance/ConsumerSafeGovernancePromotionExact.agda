module DASHI.Governance.ConsumerSafeGovernancePromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeFuturePromotionExact as Future
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- CONSUMER-SAFE GOVERNANCE PROMOTION
--
-- Governance is a thin specialization of the canonical consumer-safe future
-- promotion spine. Hard governance conditions are consequences of eligibility;
-- they are not soft Pareto axes. In particular, a cheap terminalised model is
-- outside the ranking domain rather than merely receiving a bad score.
------------------------------------------------------------------------

record GovernanceGateSystem
    (problem : MDL.ConsumerMDLProblem) : Set₁ where
  field
    PropositionLocal : MDL.Model problem → Set
    CollectiveGuiltFree : MDL.Model problem → Set
    CivilianNonSubstituting : MDL.Model problem → Set
    CorrectivelyReopenable : MDL.Model problem → Set
    Terminalised : MDL.Model problem → Set

    eligiblePropositionLocal :
      ∀ {model} → MDL.Eligible problem model → PropositionLocal model
    eligibleCollectiveGuiltFree :
      ∀ {model} → MDL.Eligible problem model → CollectiveGuiltFree model
    eligibleCivilianNonSubstituting :
      ∀ {model} → MDL.Eligible problem model → CivilianNonSubstituting model
    eligibleCorrectivelyReopenable :
      ∀ {model} → MDL.Eligible problem model → CorrectivelyReopenable model
    eligibleNotTerminalised :
      ∀ {model} → MDL.Eligible problem model → Terminalised model → ⊥

open GovernanceGateSystem public

record ConsumerSafeGovernancePromotion
    {problem : MDL.ConsumerMDLProblem}
    (costs : MDL.CostHyperfabric problem)
    (coarse fine : MDL.Model problem)
    {State Action Surface Provenance QueryKey Answer : Set}
    (system : Dependency.DependentActionSystem State Action)
    (surface : State → Surface)
    (provenance : State → Provenance)
    (Rule : Set)
    (semantics : Query.QuerySemantics State QueryKey Answer)
    (query : QueryKey)
    (Realises : MDL.Model problem → (State → Surface × Provenance) → Set)
    (gates : GovernanceGateSystem problem) : Set₁ where
  constructor consumer-safe-governance-promotion
  field
    futureSafe :
      Future.ConsumerSafeFuturePromotion
        costs coarse fine system surface provenance Rule semantics query Realises

open ConsumerSafeGovernancePromotion public

selectedGovernanceEligible :
  ∀ {problem costs coarse fine State Action Surface Provenance QueryKey Answer
      system surface provenance Rule semantics query Realises gates} →
  ConsumerSafeGovernancePromotion
    {problem} costs coarse fine
    {State} {Action} {Surface} {Provenance} {QueryKey} {Answer}
    system surface provenance Rule semantics query Realises gates →
  MDL.Eligible problem fine
selectedGovernanceEligible promotion =
  Future.selectedModelEligible (futureSafe promotion)

selectedGovernancePropositionLocal :
  ∀ {problem costs coarse fine State Action Surface Provenance QueryKey Answer
      system surface provenance Rule semantics query Realises gates} →
  ConsumerSafeGovernancePromotion
    {problem} costs coarse fine
    {State} {Action} {Surface} {Provenance} {QueryKey} {Answer}
    system surface provenance Rule semantics query Realises gates →
  PropositionLocal gates fine
selectedGovernancePropositionLocal promotion =
  eligiblePropositionLocal _ (selectedGovernanceEligible promotion)

selectedGovernanceCorrectivelyReopenable :
  ∀ {problem costs coarse fine State Action Surface Provenance QueryKey Answer
      system surface provenance Rule semantics query Realises gates} →
  ConsumerSafeGovernancePromotion
    {problem} costs coarse fine
    {State} {Action} {Surface} {Provenance} {QueryKey} {Answer}
    system surface provenance Rule semantics query Realises gates →
  CorrectivelyReopenable gates fine
selectedGovernanceCorrectivelyReopenable promotion =
  eligibleCorrectivelyReopenable _ (selectedGovernanceEligible promotion)

selectedGovernanceNotTerminalised :
  ∀ {problem costs coarse fine State Action Surface Provenance QueryKey Answer
      system surface provenance Rule semantics query Realises gates} →
  (promotion : ConsumerSafeGovernancePromotion
    {problem} costs coarse fine
    {State} {Action} {Surface} {Provenance} {QueryKey} {Answer}
    system surface provenance Rule semantics query Realises gates) →
  Terminalised gates fine → ⊥
selectedGovernanceNotTerminalised promotion =
  eligibleNotTerminalised _ (selectedGovernanceEligible promotion)

------------------------------------------------------------------------
-- General hard-gate theorem: no terminalised model can become Pareto-admissible
-- merely by being cheap on the declared cost axes.
------------------------------------------------------------------------

terminalisedModelCannotBeParetoAdmissible :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {gates : GovernanceGateSystem problem}
    {model : MDL.Model problem} →
  MDL.ParetoAdmissible costs model →
  Terminalised gates model →
  ⊥
terminalisedModelCannotBeParetoAdmissible pareto terminalised =
  eligibleNotTerminalised _ (MDL.selectedEligible pareto) terminalised

record ConsumerSafeGovernancePromotionBoundary : Set where
  constructor consumer-safe-governance-promotion-boundary
  field
    propositionLocalityIsHardGate : Bool
    collectiveGuiltFreedomIsHardGate : Bool
    civilianNonSubstitutionIsHardGate : Bool
    correctiveReopeningIsHardGate : Bool
    terminalisedCandidateCanWinByLowCost : Bool
    futureSafetyIsSeparateFromStaticPareto : Bool
    promotionCreatesPoliticalAuthority : Bool

canonicalConsumerSafeGovernancePromotionBoundary :
  ConsumerSafeGovernancePromotionBoundary
canonicalConsumerSafeGovernancePromotionBoundary =
  consumer-safe-governance-promotion-boundary
    true true true true false true false
