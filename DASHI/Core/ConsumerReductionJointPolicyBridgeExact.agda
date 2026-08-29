module DASHI.Core.ConsumerReductionJointPolicyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint

------------------------------------------------------------------------
-- CONSUMER-REDUCTION ESCALATION -> JOINT FIDELITY POLICY
--
-- A consumer-specific reduction counterexample can justify moving to a richer
-- model candidate.  The move changes model state only; empirical hypothesis
-- refinement still requires an evidence-producing move elsewhere in the joint
-- policy.
------------------------------------------------------------------------

reductionEscalationAsFidelityMove :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {from to : Search.ReductionCandidate
      Fine Action Observation fineStep observe} →
  Search.ReductionEscalationEdge from to →
  (transitionCost : Nat) →
  String →
  Joint.FidelityMove
    (Search.ReductionCandidate Fine Action Observation fineStep observe)
    from
reductionEscalationAsFidelityMove {to = to} edge transitionCost costReference =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      transitionCost
      (Search.escalationReasonReference edge)
      costReference
      "consumer-specific escalation from retained counterexample")
    refl
    to
    (Search.escalationReasonReference edge)
    (Search.retainedCounterexampleReference edge)

------------------------------------------------------------------------
-- The edge itself still carries the substantive reason for escalation: the
-- cheaper model was refuted for the declared consumer and the declared cost
-- order is nondecreasing.  The transition-cost parameter above is intentionally
-- separate from Search.costRank, which is only a candidate ordering.
------------------------------------------------------------------------

record ReductionJointPolicyBridgeBoundary : Set where
  constructor reductionJointPolicyBridgeBoundary
  field
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
  reductionJointPolicyBridgeBoundary false refl true refl false refl
