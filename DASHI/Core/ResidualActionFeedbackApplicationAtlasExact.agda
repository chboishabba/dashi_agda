module DASHI.Core.ResidualActionFeedbackApplicationAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismDiscriminationApplicationAtlasExact as Atlas
import DASHI.Core.ResidualActionPolicyExact as Action

------------------------------------------------------------------------
-- CROSS-DOMAIN FEEDBACK ATLAS
--
-- Extends the residual-action atlas with the observation that must follow an
-- admitted action before the residual/model state is updated.  These are
-- theorem-shape templates only; domain evidence and authority remain local.
------------------------------------------------------------------------

record FeedbackTemplate : Set where
  constructor feedbackTemplate
  field
    circumstance : Atlas.CircumstanceClass
    actionKind : Action.ResidualActionKind
    postActionObservation : String
    updateTarget : String
    stopCondition : String
    safetyOrAuthorityBoundary : String

open FeedbackTemplate public

biochemicalFeedback : FeedbackTemplate
biochemicalFeedback = feedbackTemplate
  Atlas.biochemicalMechanism Action.perturb
  "matched post-perturbation molecular, regulatory and phenotype panel"
  "mechanism residual and dependency-reachable biochemical carriers"
  "declared causal/consumer criterion rather than perturbation occurrence itself"
  "laboratory execution, biosafety and same-preparation provenance remain independent"

engineeringFeedback : FeedbackTemplate
engineeringFeedback = feedbackTemplate
  Atlas.engineeringFaultDiagnosis Action.measure
  "calibrated post-test sensor/component state"
  "fault residual and only affected component/sensor dependencies"
  "safe repair decision or fault discrimination sufficient for the declared consumer"
  "diagnostic test does not itself authorise repair, shutdown or unsafe loading"

softwareFeedback : FeedbackTemplate
softwareFeedback = feedbackTemplate
  Atlas.softwareFailureDiagnosis Action.perturb
  "reproduction outcome, trace and regression-test result after controlled change"
  "dependency/configuration/data/concurrency residual"
  "consumer-relevant fix validated in declared environment"
  "test mutation does not authorise production deployment"

ecologicalFeedback : FeedbackTemplate
ecologicalFeedback = feedbackTemplate
  Atlas.ecologicalCausalAttribution Action.measure
  "matched temporal/comparator observation after sampling or permitted intervention"
  "driver-specific ecological residual"
  "declared attribution or monitoring decision sufficiently supported"
  "ethical and regulatory intervention authority remains separate"

financialFeedback : FeedbackTemplate
financialFeedback = feedbackTemplate
  Atlas.financialModelDiscrimination Action.measure
  "out-of-sample/stress/decomposition result with lineage"
  "exposure/liquidity/model/data residual"
  "declared risk/model-governance consumer closes"
  "diagnostic update does not authorise trading or capital allocation"

legalFeedback : FeedbackTemplate
legalFeedback = feedbackTemplate
  Atlas.legalCausalExplanation Action.reopen
  "new authority/evidence/procedural record and provenance"
  "doctrine/evidence/procedure/authority residual"
  "jurisdiction-specific legal consumer closes under admissible authority"
  "generic residual calculus does not create legal authority or remedy"

historicalFeedback : FeedbackTemplate
historicalFeedback = feedbackTemplate
  Atlas.historicalProvenanceExplanation Action.reopen
  "new source, custody, succession or event-time receipt"
  "dependency-reachable provenance/custody residual"
  "declared historical consumer closes without forcing total narrative identity"
  "new source can revise explanation but does not by itself establish intent"

sensorFusionFeedback : FeedbackTemplate
sensorFusionFeedback = feedbackTemplate
  Atlas.sensorFusionDiagnosis Action.measure
  "held-out sensor or independent reference observation after recalibration"
  "sensor/calibration/timing dependency residual"
  "fused decision/estimate is robust for the declared consumer"
  "one post-action agreement does not prove unique latent sensor state"

record ResidualActionFeedbackAtlasBoundary : Set where
  constructor residualActionFeedbackAtlasBoundary
  field
    actionOccurrenceEqualsSuccessfulOutcome : Bool
    actionOccurrenceEqualsSuccessfulOutcomeIsFalse :
      actionOccurrenceEqualsSuccessfulOutcome ≡ false
    successfulOutcomeEqualsUniqueMechanism : Bool
    successfulOutcomeEqualsUniqueMechanismIsFalse :
      successfulOutcomeEqualsUniqueMechanism ≡ false
    everyActionNeedsDomainAppropriatePostObservation : Bool
    everyActionNeedsDomainAppropriatePostObservationIsTrue :
      everyActionNeedsDomainAppropriatePostObservation ≡ true
    postActionEvidenceMaySelectDifferentResidualAction : Bool
    postActionEvidenceMaySelectDifferentResidualActionIsTrue :
      postActionEvidenceMaySelectDifferentResidualAction ≡ true

canonicalResidualActionFeedbackAtlasBoundary : ResidualActionFeedbackAtlasBoundary
canonicalResidualActionFeedbackAtlasBoundary =
  residualActionFeedbackAtlasBoundary false refl false refl true refl true refl
