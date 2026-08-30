module DASHI.Core.ConsumerReductionJointPolicyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint

------------------------------------------------------------------------
-- CONSUMER-REDUCTION ESCALATION -> JOINT FIDELITY POLICY
--
-- ReductionCandidate itself lives in Set₁ because it contains a code type.
-- The joint planner intentionally keeps its runtime model coordinate first-order
-- (`ModelCode : Set`).  This bridge therefore transports the proof-bearing
-- escalation edge onto an application-declared first-order model code rather
-- than pretending the full candidate record is the runtime state.
------------------------------------------------------------------------

reductionEscalationAsFidelityMove :
  ∀ {Fine Action Observation ModelCode}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {from to : Search.ReductionCandidate
      Fine Action Observation fineStep observe} →
  Search.ReductionEscalationEdge from to →
  (fromCode toCode : ModelCode) →
  (transitionCost : Nat) →
  String →
  Joint.FidelityMove ModelCode fromCode
reductionEscalationAsFidelityMove edge fromCode toCode transitionCost costReference =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      transitionCost
      (Search.escalationReasonReference edge)
      costReference
      "consumer-specific escalation from retained counterexample")
    refl
    toCode
    (Search.escalationReasonReference edge)
    (Search.retainedCounterexampleReference edge)

record ReductionJointPolicyBridgeBoundary : Set where
  constructor reductionJointPolicyBridgeBoundary
  field
    fullReductionCandidateMustBeRuntimeModelState : Bool
    fullReductionCandidateMustBeRuntimeModelStateIsFalse :
      fullReductionCandidateMustBeRuntimeModelState ≡ false

    candidateCostRankIsAutomaticallyIncrementalRuntimeCost : Bool
    candidateCostRankIsAutomaticallyIncrementalRuntimeCostIsFalse :
      candidateCostRankIsAutomaticallyIncrementalRuntimeCost ≡ false

    reductionCounterexampleCanJustifyFidelityEscalation : Bool
    reductionCounterexampleCanJustifyFidelityEscalationIsTrue :
      reductionCounterexampleCanJustifyFidelityEscalation ≡ true

    fidelityEscalationItselfIsNewEmpiricalEvidence : Bool
    fidelityEscalationItselfIsNewEmpiricalEvidenceIsFalse :
      fidelityEscalationItselfIsNewEmpiricalEvidence ≡ false

canonicalReductionJointPolicyBridgeBoundary : ReductionJointPolicyBridgeBoundary
canonicalReductionJointPolicyBridgeBoundary =
  reductionJointPolicyBridgeBoundary
    false refl false refl true refl false refl
