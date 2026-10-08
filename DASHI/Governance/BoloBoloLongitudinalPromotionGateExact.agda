module DASHI.Governance.BoloBoloLongitudinalPromotionGateExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloEmpiricalPromotionGateExact as Promotion
import DASHI.Governance.BoloBoloDynamicInstitutionalFeedbackBridgeExact as Dynamic

------------------------------------------------------------------------
-- LONGITUDINAL PROMOTION GATE.
--
-- A validated meaningful snapshot comparison is still weaker than a claim
-- about institutional performance through adaptation. Long-run promotion must
-- carry evidence that realised topology, actor response, institutional version
-- and model revision have been audited across a declared longitudinal window.
------------------------------------------------------------------------

record LongitudinalValidationObligations : Set₁ where
  constructor longitudinalValidationObligations
  field
    RepeatedMeasurementPassed : Set
    repeatedMeasurementWitness : RepeatedMeasurementPassed

    RealisedTopologyAuditPassed : Set
    realisedTopologyAuditWitness : RealisedTopologyAuditPassed

    ActorAdaptationAuditPassed : Set
    actorAdaptationAuditWitness : ActorAdaptationAuditPassed

    InstitutionalVersionAuditPassed : Set
    institutionalVersionAuditWitness : InstitutionalVersionAuditPassed

    EvidenceTriggeredReopeningPolicyApplied : Set
    reopeningPolicyWitness : EvidenceTriggeredReopeningPolicyApplied

    LongitudinalWindowPredeclared : Set
    longitudinalWindowWitness : LongitudinalWindowPredeclared

open LongitudinalValidationObligations public

record LongitudinalValidatedMeaningfulBoloAdvantage
  (threshold : Nat)
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor longitudinalValidatedMeaningfulBoloAdvantage
  field
    snapshotCertificate :
      Promotion.ValidatedMeaningfulBoloCoordinationAdvantage threshold model
    longitudinalValidation : LongitudinalValidationObligations

open LongitudinalValidatedMeaningfulBoloAdvantage public

snapshotFromLongitudinalAdvantage :
  ∀ {threshold model} →
  LongitudinalValidatedMeaningfulBoloAdvantage threshold model →
  Promotion.ValidatedMeaningfulBoloCoordinationAdvantage threshold model
snapshotFromLongitudinalAdvantage certificate =
  snapshotCertificate certificate

record LongitudinalValidatedMeaningfulBoloDisadvantage
  (threshold : Nat)
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor longitudinalValidatedMeaningfulBoloDisadvantage
  field
    snapshotCertificate :
      Promotion.ValidatedMeaningfulBoloCoordinationDisadvantage threshold model
    longitudinalValidation : LongitudinalValidationObligations

open LongitudinalValidatedMeaningfulBoloDisadvantage public

snapshotFromLongitudinalDisadvantage :
  ∀ {threshold model} →
  LongitudinalValidatedMeaningfulBoloDisadvantage threshold model →
  Promotion.ValidatedMeaningfulBoloCoordinationDisadvantage threshold model
snapshotFromLongitudinalDisadvantage certificate =
  snapshotCertificate certificate

record LongitudinalPromotionBoundary : Set where
  constructor longitudinalPromotionBoundary
  field
    snapshotMeaningfulWinAutomaticallyEstablishesLongRunWin : Bool
    snapshotMeaningfulLossAutomaticallyEstablishesLongRunLoss : Bool
    repeatedMeasurementRequired : Bool
    realisedTopologyAuditRequired : Bool
    actorAdaptationAuditRequired : Bool
    institutionalVersionAuditRequired : Bool
    evidenceTriggeredModelReopeningRequired : Bool
    longitudinalWindowMustBePredeclared : Bool
    longRunAdvantageCreatesPoliticalLegitimacy : Bool
    longRunAdvantageProvesEcologicalViability : Bool

open LongitudinalPromotionBoundary public

canonicalLongitudinalPromotionBoundary : LongitudinalPromotionBoundary
canonicalLongitudinalPromotionBoundary =
  longitudinalPromotionBoundary
    false false
    true true true true true true
    false false

canonicalLongitudinalDynamicObligations : Dynamic.DynamicBoloEvaluationObligations
canonicalLongitudinalDynamicObligations =
  Dynamic.canonicalDynamicBoloEvaluationObligations

canonicalLongitudinalPromotionReceipt : GenericReceipt.GenericReceipt
canonicalLongitudinalPromotionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo longitudinal adaptive-institution promotion gate"
    "DASHI.Governance.BoloBoloLongitudinalPromotionGateExact"
    "LongitudinalValidatedMeaningfulBoloAdvantage / LongitudinalValidatedMeaningfulBoloDisadvantage / canonicalLongitudinalPromotionBoundary"
    "adds a stronger promotion tier above validated meaningful snapshot comparison: a long-run coordination claim must also carry repeated measurement, realised-topology audit, actor-adaptation audit, institutional-version audit, evidence-triggered model reopening and a predeclared longitudinal window"
    "snapshot validation remains necessary but not sufficient for long-run institutional performance, and even longitudinal coordination advantage creates neither political legitimacy nor ecological viability"
    "agda -i . DASHI/Governance/BoloBoloLongitudinalPromotionGateRegression.agda"
