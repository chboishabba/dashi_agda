module DASHI.Core.ConsumerAdequacyJointPolicyBidiCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerDecisionAdequacyFromReductionExact as Adequacy
import DASHI.Core.ConsumerReductionJointPolicyBridgeExact as Escalation
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust

------------------------------------------------------------------------
-- BIDI COMPILER
--
-- Forward direction:
--   exact ROM / approximate margin certificate
--     -> rich decision adequacy
--     -> first-order policy token
--     -> robust + authority -> act.
--
-- Backward/failure direction:
--   consumer-specific counterexample
--     -> reduction escalation edge
--     -> runtime fidelity move.
------------------------------------------------------------------------

CertifiedAdequacyJointPolicy :
  ∀ {ModelState Fine Action Summary Intervention Hypothesis Outcome}
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set)
    (ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set)
    (interface : Adequacy.FirstOrderAdequacyInterface
      ExactRealises ApproxRealises) →
  (Hypothesis → Set) → ModelState → Set₁
CertifiedAdequacyJointPolicy system Authority ExactRealises ApproxRealises
    interface live model =
  Joint.JointSequentialPolicy
    system Authority ModelState
    (Adequacy.Token interface)
    live model

actFromDerivedAdequacy :
  ∀ {ModelState Fine Action Summary Intervention Hypothesis Outcome}
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set}
    {ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set}
    (interface : Adequacy.FirstOrderAdequacyInterface
      ExactRealises ApproxRealises)
    {live : Hypothesis → Set}
    {model : ModelState}
    {intervention : Intervention} →
  Robust.RobustlyNoWorseThanBaseline system live intervention →
  Adequacy.DerivedDecisionAdequacy
    ExactRealises ApproxRealises model intervention →
  Authority intervention →
  CertifiedAdequacyJointPolicy
    system Authority ExactRealises ApproxRealises interface live model
actFromDerivedAdequacy {intervention = intervention}
    interface robust proof authority =
  Joint.actNow
    intervention
    robust
    (Adequacy.proofToToken interface proof)
    authority

exactROMActBranch :
  ∀ {ModelState Fine Action Summary Intervention Hypothesis Outcome}
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set}
    {ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set}
    (interface : Adequacy.FirstOrderAdequacyInterface
      ExactRealises ApproxRealises)
    {live : Hypothesis → Set}
    {runtimeModel : ModelState}
    {intervention : Intervention}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Summary) →
  ExactRealises runtimeModel rom →
  (decide : Summary → Intervention) →
  Adequacy.ExactDecisionAdequacy rom decide intervention →
  Robust.RobustlyNoWorseThanBaseline system live intervention →
  Authority intervention →
  CertifiedAdequacyJointPolicy
    system Authority ExactRealises ApproxRealises interface live runtimeModel
exactROMActBranch interface rom realised decide decisionAdequacy robust authority =
  actFromDerivedAdequacy interface robust
    (Adequacy.exactAdequate rom realised decide decisionAdequacy)
    authority

approximateROMActBranch :
  ∀ {ModelState Fine Action Summary Intervention Hypothesis Outcome}
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {ExactRealises :
      ModelState →
      Reduction.ConsumerRelativeReduction Fine Action Summary → Set}
    {ApproxRealises :
      ModelState →
      Approx.ApproximateTraceReduction Fine Action Summary → Set}
    (interface : Adequacy.FirstOrderAdequacyInterface
      ExactRealises ApproxRealises)
    {live : Hypothesis → Set}
    {runtimeModel : ModelState}
    {intervention : Intervention}
    (model : Approx.ApproximateTraceReduction Fine Action Summary) →
  ApproxRealises runtimeModel model →
  (decide : Summary → Intervention) →
  Adequacy.ApproximateDecisionAdequacy model decide intervention →
  Robust.RobustlyNoWorseThanBaseline system live intervention →
  Authority intervention →
  CertifiedAdequacyJointPolicy
    system Authority ExactRealises ApproxRealises interface live runtimeModel
approximateROMActBranch interface model realised decide decisionAdequacy robust authority =
  actFromDerivedAdequacy interface robust
    (Adequacy.approximateAdequate model realised decide decisionAdequacy)
    authority

counterexampleOpensFidelityBranch :
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
counterexampleOpensFidelityBranch =
  Escalation.reductionEscalationAsFidelityMove

record ConsumerAdequacyBidiCompilerBoundary : Set where
  constructor consumerAdequacyBidiCompilerBoundary
  field
    exactCertificateCanFeedPolicyAdequacy : Bool
    exactCertificateCanFeedPolicyAdequacyIsTrue :
      exactCertificateCanFeedPolicyAdequacy ≡ true

    approximateMarginCertificateCanFeedPolicyAdequacy : Bool
    approximateMarginCertificateCanFeedPolicyAdequacyIsTrue :
      approximateMarginCertificateCanFeedPolicyAdequacy ≡ true

    missingCertificateAloneOpensFidelityBranch : Bool
    missingCertificateAloneOpensFidelityBranchIsFalse :
      missingCertificateAloneOpensFidelityBranch ≡ false

    consumerCounterexampleCanOpenFidelityBranch : Bool
    consumerCounterexampleCanOpenFidelityBranchIsTrue :
      consumerCounterexampleCanOpenFidelityBranch ≡ true

    robustnessOrAdequacyCreatesAuthority : Bool
    robustnessOrAdequacyCreatesAuthorityIsFalse :
      robustnessOrAdequacyCreatesAuthority ≡ false

canonicalConsumerAdequacyBidiCompilerBoundary :
  ConsumerAdequacyBidiCompilerBoundary
canonicalConsumerAdequacyBidiCompilerBoundary =
  consumerAdequacyBidiCompilerBoundary
    true refl true refl false refl true refl false refl
