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
-- Forward:
--   candidate -> exact certificate / approximate margin certificate
--     -> decision adequacy -> robustness -> authority -> act.
-- Backward:
--   candidate -> consumer counterexample -> escalation edge -> fidelity move.
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
  Joint.actNow intervention robust
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

------------------------------------------------------------------------
-- Exact candidate-search receipt -> exact ROM -> decision adequacy -> act.
-- This closes the forward chain from the actual ReductionCandidate surface.
------------------------------------------------------------------------

certifiedCandidateActBranch :
  ∀ {ModelState Fine Action Summary Intervention Hypothesis Outcome}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Summary}
    {candidate : Search.ReductionCandidate Fine Action Summary fineStep observe}
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
    (certificate : Search.CandidateCertification candidate) →
  ExactRealises runtimeModel (Search.certificationAsReduction certificate) →
  (decide : Summary → Intervention) →
  Adequacy.ExactDecisionAdequacy
    (Search.certificationAsReduction certificate) decide intervention →
  Robust.RobustlyNoWorseThanBaseline system live intervention →
  Authority intervention →
  CertifiedAdequacyJointPolicy
    system Authority ExactRealises ApproxRealises interface live runtimeModel
certifiedCandidateActBranch interface certificate realised decide adequacy robust authority =
  exactROMActBranch interface
    (Search.certificationAsReduction certificate)
    realised decide adequacy robust authority

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
    candidateCertificationCanFeedPolicyAdequacy : Bool
    candidateCertificationCanFeedPolicyAdequacyIsTrue :
      candidateCertificationCanFeedPolicyAdequacy ≡ true
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
    true refl true refl true refl false refl true refl false refl
