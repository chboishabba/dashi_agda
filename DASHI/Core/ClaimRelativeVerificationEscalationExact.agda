module DASHI.Core.ClaimRelativeVerificationEscalationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.HumanReviewCore as Review
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- CLAIM-RELATIVE VERIFICATION / ESCALATION CORE
--
-- DASHI-owned synthesis over existing repository-native owners.
--
-- External research may motivate concrete policy choices, but supplies no
-- theorem authority here.  In particular, weak/strong verification,
-- natural-language -> formal-spec compilation, constrained decoding and
-- abstention benchmarks remain externally attributed empirical/formal results.
-- This module only provides the repo-native adapter surface needed to test such
-- ideas without collapsing specification fidelity, verification, review,
-- empirical outcome or authority into one another.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source/intention -> specification is its own obligation.
------------------------------------------------------------------------

record SpecificationTranslationReceipt
    (Source Specification Consumer : Set) : Set₁ where
  constructor specification-translation-receipt
  field
    source : Source
    specification : Specification
    consumer : Consumer
    TranslationAdequate : Set
    translationAdequate : TranslationAdequate
    sourceReference : String
    specificationReference : String
    consumerReference : String
    translationMethodReference : String

open SpecificationTranslationReceipt public

------------------------------------------------------------------------
-- 2. Weak verification is observable evidence, not terminal authority.
------------------------------------------------------------------------

data WeakVerificationStatus : Set where
  weakPass : WeakVerificationStatus
  weakFail : WeakVerificationStatus
  weakUnknown : WeakVerificationStatus
  weakOutOfDomain : WeakVerificationStatus

record WeakVerificationReceipt (Specification : Set) : Set where
  constructor weak-verification-receipt
  field
    checkedSpecification : Specification
    weakStatus : WeakVerificationStatus
    weakVerifierReference : String
    weakEvidenceReference : String

open WeakVerificationReceipt public

------------------------------------------------------------------------
-- 3. Escalation targets are typed and preserve their native authority.
------------------------------------------------------------------------

data EscalationTarget : Set where
  strongVerifierTarget : EscalationTarget
  evidenceAcquisitionTarget : EscalationTarget
  executionOrSimulationTarget : EscalationTarget
  humanReviewTarget : EscalationTarget


data EscalationPayload : EscalationTarget → Set₁ where
  strongVerifierPayload :
    (Receipt : Set) →
    Receipt →
    String →
    EscalationPayload strongVerifierTarget

  evidenceAcquisitionPayload :
    (target : Acquisition.AcquisitionTarget) →
    Acquisition.AcquisitionObligation target →
    EscalationPayload evidenceAcquisitionTarget

  executionOrSimulationPayload :
    (Receipt : Set) →
    Receipt →
    String →
    EscalationPayload executionOrSimulationTarget

  humanReviewPayload :
    Review.GenericHumanReviewReceipt →
    Review.ExactReviewItemBinding →
    EscalationPayload humanReviewTarget

record EscalationReceipt
    {Specification : Set}
    (weak : WeakVerificationReceipt Specification) : Set₁ where
  constructor escalation-receipt
  field
    target : EscalationTarget
    payload : EscalationPayload target
    escalationReasonReference : String
    priorFrontierReference : String
    nextFrontierReference : String

open EscalationReceipt public

------------------------------------------------------------------------
-- 4. The object entering verification must already be eligible for the
-- declared consumer.  Cheap code / rhetorically rich output cannot bypass
-- admissibility or consumer adequacy.
------------------------------------------------------------------------

record EligibleClaimCase
    (problem : MDL.ConsumerMDLProblem)
    (Source Specification Consumer : Set) : Set₁ where
  constructor eligible-claim-case
  field
    translation : SpecificationTranslationReceipt Source Specification Consumer
    model : MDL.Model problem
    modelEligible : MDL.Eligible problem model
    caseReference : String

open EligibleClaimCase public

------------------------------------------------------------------------
-- 5. Frontier archaeology / narrative is advisory only.  This is the ABI by
-- which repository-intelligence tooling can guide search without becoming
-- theorem or empirical authority.
------------------------------------------------------------------------

record FrontierAdvisoryReceipt : Set where
  constructor frontier-advisory-receipt
  field
    historyReference : String
    currentFrontierReference : String
    historyComplete : Bool
    advisoryReference : String
    advisoryOnly : Bool
    advisoryOnlyIsTrue : advisoryOnly ≡ true

open FrontierAdvisoryReceipt public

------------------------------------------------------------------------
-- 6. Same-object held-out experiment adapter.  The robust experiment owner
-- remains canonical for the held-out protocol; this layer only binds the
-- declared object and intervention used by the claim-relative evaluation.
------------------------------------------------------------------------

record SameObjectHeldOutEvaluation
    (Object Intervention Repair Training HeldOut Prediction : Set) : Set₁ where
  constructor same-object-held-out-evaluation
  field
    object : Object
    intervention : Intervention
    protocol : Robust.HeldOutRepair Repair Training HeldOut Prediction
    sameObjectReceipt : Set
    sameObject : sameObjectReceipt
    sameInterventionReceipt : Set
    sameIntervention : sameInterventionReceipt
    evaluationReference : String

open SameObjectHeldOutEvaluation public

------------------------------------------------------------------------
-- 7. Anti-Goodhart surface: validator and consumer observations coexist but
-- neither is defined as the other.  Concrete experiments may correlate them;
-- this generic layer does not.
------------------------------------------------------------------------

record ValidatorConsumerObservation
    (ValidatorObservation ConsumerObservation : Set) : Set where
  constructor validator-consumer-observation
  field
    validatorObservation : ValidatorObservation
    consumerObservation : ConsumerObservation
    validatorReference : String
    consumerOutcomeReference : String

open ValidatorConsumerObservation public

------------------------------------------------------------------------
-- 8. End-to-end claim-relative evaluation packet.  This is the intended
-- cross-program harness surface: source/spec translation, eligible model,
-- weak check, optional escalation, same-object held-out test and separated
-- validator/consumer outcomes.
------------------------------------------------------------------------

record ClaimRelativeEvaluationPacket
    (problem : MDL.ConsumerMDLProblem)
    (Source Specification Consumer : Set)
    (Object Intervention Repair Training HeldOut Prediction : Set)
    (ValidatorObservation ConsumerObservation : Set) : Set₁ where
  constructor claim-relative-evaluation-packet
  field
    claimCase : EligibleClaimCase problem Source Specification Consumer
    weakReceipt : WeakVerificationReceipt Specification
    weakChecksSameSpecification :
      checkedSpecification weakReceipt ≡
      specification (translation claimCase)
    frontierAdvisory : FrontierAdvisoryReceipt
    heldOutEvaluation :
      SameObjectHeldOutEvaluation
        Object Intervention Repair Training HeldOut Prediction
    observations :
      ValidatorConsumerObservation ValidatorObservation ConsumerObservation
    packetReference : String

open ClaimRelativeEvaluationPacket public

------------------------------------------------------------------------
-- Re-export the already-canonical active BIDI orchestration boundaries that
-- matter for this compiler.  We do not define a competing agent loop.
------------------------------------------------------------------------

bidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
bidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

robustInterventionDoesNotCreateAuthority :
  Bidi.robustInterventionCreatesItsOwnAuthority bidiBoundary ≡ false
robustInterventionDoesNotCreateAuthority = refl

consumerMayCloseBeforeFullWorldIdentification :
  Bidi.consumerClosureMayPrecedeFullWorldIdentification bidiBoundary ≡ true
consumerMayCloseBeforeFullWorldIdentification = refl

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record ClaimRelativeVerificationBoundary : Set where
  constructor claim-relative-verification-boundary
  field
    formalVerificationCreatesTranslationAdequacy : Bool
    formalVerificationCreatesTranslationAdequacyIsFalse :
      formalVerificationCreatesTranslationAdequacy ≡ false

    weakVerificationCreatesDecisionAuthority : Bool
    weakVerificationCreatesDecisionAuthorityIsFalse :
      weakVerificationCreatesDecisionAuthority ≡ false

    humanReviewCreatesClaimTruth : Bool
    humanReviewCreatesClaimTruthIsFalse :
      humanReviewCreatesClaimTruth ≡ false

    validatorSuccessCreatesConsumerSuccess : Bool
    validatorSuccessCreatesConsumerSuccessIsFalse :
      validatorSuccessCreatesConsumerSuccess ≡ false

    boundedHistoryAuthorizesNegativeDiscovery : Bool
    boundedHistoryAuthorizesNegativeDiscoveryIsFalse :
      boundedHistoryAuthorizesNegativeDiscovery ≡ false

    evidenceAcquisitionReopensOnlyAffectedConsumers : Bool
    evidenceAcquisitionReopensOnlyAffectedConsumersIsTrue :
      evidenceAcquisitionReopensOnlyAffectedConsumers ≡ true

    abstentionMayOccurBeforeIrreversibleAction : Bool
    abstentionMayOccurBeforeIrreversibleActionIsTrue :
      abstentionMayOccurBeforeIrreversibleAction ≡ true

    heldOutFitCreatesMechanismIdentity : Bool
    heldOutFitCreatesMechanismIdentityIsFalse :
      heldOutFitCreatesMechanismIdentity ≡ false

    eligibleRepresentationCreatesWorldCompleteness : Bool
    eligibleRepresentationCreatesWorldCompletenessIsFalse :
      eligibleRepresentationCreatesWorldCompleteness ≡ false

    reading : String

canonicalClaimRelativeVerificationBoundary : ClaimRelativeVerificationBoundary
canonicalClaimRelativeVerificationBoundary =
  claim-relative-verification-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Claim-relative verification separates source-to-specification adequacy, representation eligibility, weak checking, selective escalation, human review, targeted evidence acquisition, same-object held-out evaluation and downstream consumer outcome.  Each stage retains its own authority; passing one stage does not manufacture the others."
