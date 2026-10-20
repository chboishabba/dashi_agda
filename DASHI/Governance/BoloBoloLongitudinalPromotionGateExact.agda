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
-- carry repeated same-polarity meaningful certificates plus evidence that
-- realised topology, actor response, institutional version and model revision
-- have been audited across a predeclared longitudinal window.
------------------------------------------------------------------------

data AtLeastTwo {A : Set₁} : List A → Set₁ where
  atLeastTwo : ∀ x y xs → AtLeastTwo (x ∷ y ∷ xs)

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
    periodCertificates :
      List (Promotion.ValidatedMeaningfulBoloCoordinationAdvantage threshold model)
    atLeastTwoCertifiedPeriods : AtLeastTwo periodCertificates
    longitudinalValidation : LongitudinalValidationObligations

open LongitudinalValidatedMeaningfulBoloAdvantage public

record LongitudinalValidatedMeaningfulBoloDisadvantage
  (threshold : Nat)
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor longitudinalValidatedMeaningfulBoloDisadvantage
  field
    periodCertificates :
      List (Promotion.ValidatedMeaningfulBoloCoordinationDisadvantage threshold model)
    atLeastTwoCertifiedPeriods : AtLeastTwo periodCertificates
    longitudinalValidation : LongitudinalValidationObligations

open LongitudinalValidatedMeaningfulBoloDisadvantage public

record LongitudinalPromotionBoundary : Set where
  constructor longitudinalPromotionBoundary
  field
    snapshotMeaningfulWinAutomaticallyEstablishesLongRunWin : Bool
    snapshotMeaningfulLossAutomaticallyEstablishesLongRunLoss : Bool
    atLeastTwoCertifiedPeriodsRequired : Bool
    repeatedSamePolarityRequired : Bool
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
    true true true true true true true true
    false false

canonicalLongitudinalDynamicObligations : Dynamic.DynamicBoloEvaluationObligations
canonicalLongitudinalDynamicObligations =
  Dynamic.canonicalDynamicBoloEvaluationObligations

canonicalLongitudinalPromotionReceipt : GenericReceipt.GenericReceipt
canonicalLongitudinalPromotionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo longitudinal adaptive-institution promotion gate"
    "DASHI.Governance.BoloBoloLongitudinalPromotionGateExact"
    "LongitudinalValidatedMeaningfulBoloAdvantage / LongitudinalValidatedMeaningfulBoloDisadvantage / AtLeastTwo / canonicalLongitudinalPromotionBoundary"
    "adds a stronger promotion tier above validated meaningful snapshot comparison: a long-run advantage or disadvantage must include at least two same-polarity validated meaningful period certificates plus repeated measurement, realised-topology audit, actor-adaptation audit, institutional-version audit, evidence-triggered model reopening and a predeclared longitudinal window"
    "one snapshot or merely observing the institution for a long time is insufficient for a long-run performance claim, and even a repeated longitudinal coordination advantage creates neither political legitimacy nor ecological viability"
    "agda -i . DASHI/Governance/BoloBoloLongitudinalPromotionGateRegression.agda"
