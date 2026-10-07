module DASHI.Governance.BoloBoloEmpiricalPromotionGateExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Bounds
import DASHI.Governance.BoloBoloPracticalSignificanceExact as Significance
import DASHI.Governance.BoloBoloCalibrationTransferExact as Transfer

------------------------------------------------------------------------
-- VALIDATED COMPARATIVE PROMOTION GATE.
--
-- A target-qualified robust bound separation is already stronger than a point
-- estimate, but it is still only one empirical classification.  Promotion to a
-- validated comparative coordination claim additionally requires sensitivity,
-- prospective validation/replication, documentary qualification and a frozen
-- estimand/measurement definition.
------------------------------------------------------------------------

record ValidationObligations : Set₁ where
  constructor validationObligations
  field
    EstimandFrozen : Set
    estimandFrozenWitness : EstimandFrozen

    SensitivityPassed : Set
    sensitivityPassedWitness : SensitivityPassed

    DocumentaryAuditPassed : Set
    documentaryAuditPassedWitness : DocumentaryAuditPassed

    ProspectiveValidationOrReplicationPassed : Set
    prospectiveValidationOrReplicationPassedWitness : ProspectiveValidationOrReplicationPassed

open ValidationObligations public

record ValidatedBoloCoordinationAdvantage
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor validatedBoloCoordinationAdvantage
  field
    targetRobustWin : Transfer.BoloRobustCoordinationWin model
    validation : ValidationObligations

open ValidatedBoloCoordinationAdvantage public

validatedAdvantageImpliesStrictOrder :
  ∀ {model} →
  ValidatedBoloCoordinationAdvantage model →
  Bounds.StrictOrderImprovement model
validatedAdvantageImpliesStrictOrder certificate =
  Transfer.boloRobustCoordinationWinImpliesStrictCostOrder
    (targetRobustWin certificate)

------------------------------------------------------------------------
-- Symmetric falsification surface.
------------------------------------------------------------------------

record ValidatedBoloCoordinationDisadvantage
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor validatedBoloCoordinationDisadvantage
  field
    targetEvidence : Transfer.BoloTargetBoundEvidence model
    robustLossWitness : Bounds.RobustLoss (Transfer.targetBounds targetEvidence)
    validation : ValidationObligations

open ValidatedBoloCoordinationDisadvantage public

validatedDisadvantageImpliesStrictOrderLoss :
  ∀ {model} →
  ValidatedBoloCoordinationDisadvantage model →
  Bounds.StrictOrderLoss model
validatedDisadvantageImpliesStrictOrderLoss certificate =
  Bounds.robustLossImpliesStrictOrderLoss
    (Transfer.targetBounds (targetEvidence certificate))
    (robustLossWitness certificate)

------------------------------------------------------------------------
-- Stronger meaningful-promotion tier.
--
-- A strict validated difference may still be substantively negligible.  The
-- stronger certificate freezes a minimum meaningful margin before target
-- outcomes are inspected and requires a robust bound separation exceeding
-- that threshold.
------------------------------------------------------------------------

record MeaningfulValidationObligations : Set₁ where
  constructor meaningfulValidationObligations
  field
    baseValidation : ValidationObligations
    PracticalThresholdFrozen : Set
    practicalThresholdFrozenWitness : PracticalThresholdFrozen

open MeaningfulValidationObligations public

record ValidatedMeaningfulBoloCoordinationAdvantage
  (threshold : Nat)
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor validatedMeaningfulBoloCoordinationAdvantage
  field
    targetEvidence : Transfer.BoloTargetBoundEvidence model
    meaningfulWinWitness :
      Significance.RobustMeaningfulWin threshold (Transfer.targetBounds targetEvidence)
    meaningfulValidation : MeaningfulValidationObligations

open ValidatedMeaningfulBoloCoordinationAdvantage public

validatedMeaningfulAdvantageImpliesMargin :
  ∀ {threshold model} →
  ValidatedMeaningfulBoloCoordinationAdvantage threshold model →
  Significance.MeaningfulOrderImprovement threshold model
validatedMeaningfulAdvantageImpliesMargin certificate =
  Significance.robustMeaningfulWinImpliesMargin
    (Transfer.targetBounds (targetEvidence certificate))
    (meaningfulWinWitness certificate)

record ValidatedMeaningfulBoloCoordinationDisadvantage
  (threshold : Nat)
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor validatedMeaningfulBoloCoordinationDisadvantage
  field
    targetEvidence : Transfer.BoloTargetBoundEvidence model
    meaningfulLossWitness :
      Significance.RobustMeaningfulLoss threshold (Transfer.targetBounds targetEvidence)
    meaningfulValidation : MeaningfulValidationObligations

open ValidatedMeaningfulBoloCoordinationDisadvantage public

validatedMeaningfulDisadvantageImpliesMargin :
  ∀ {threshold model} →
  ValidatedMeaningfulBoloCoordinationDisadvantage threshold model →
  Significance.MeaningfulOrderLoss threshold model
validatedMeaningfulDisadvantageImpliesMargin certificate =
  Significance.robustMeaningfulLossImpliesMargin
    (Transfer.targetBounds (targetEvidence certificate))
    (meaningfulLossWitness certificate)

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record EmpiricalPromotionBoundary : Set where
  constructor empiricalPromotionBoundary
  field
    singleTargetBoundSetAutomaticallyEstablishesValidatedAdvantage : Bool
    sensitivityAnalysisRequiredForValidatedComparison : Bool
    prospectiveValidationOrReplicationRequired : Bool
    documentaryAuditRequired : Bool
    frozenEstimandRequired : Bool
    validatedRobustLossCanFalsifyCoordinationAdvantage : Bool
    validatedCoordinationAdvantageCreatesPoliticalLegitimacy : Bool
    validatedCoordinationAdvantageProvesEcologicalViability : Bool
    validatedCoordinationAdvantageEstablishesUniversalOptimality : Bool
    validatedCoordinationDisadvantageRefutesEveryPossibleBoloVariant : Bool

open EmpiricalPromotionBoundary public

canonicalEmpiricalPromotionBoundary : EmpiricalPromotionBoundary
canonicalEmpiricalPromotionBoundary =
  empiricalPromotionBoundary
    false
    true
    true
    true
    true
    true
    false
    false
    false
    false

record MeaningfulPromotionBoundary : Set where
  constructor meaningfulPromotionBoundary
  field
    practicalThresholdMustBeFrozenBeforeTargetOutcome : Bool
    strictValidatedDifferenceAutomaticallyCountsAsMeaningful : Bool
    meaningfulValidatedAdvantageCreatesPoliticalLegitimacy : Bool
    meaningfulValidatedLossRefutesEveryNestedVariant : Bool

open MeaningfulPromotionBoundary public

canonicalMeaningfulPromotionBoundary : MeaningfulPromotionBoundary
canonicalMeaningfulPromotionBoundary =
  meaningfulPromotionBoundary true false false false

canonicalBoloEmpiricalPromotionGateReceipt : GenericReceipt.GenericReceipt
canonicalBoloEmpiricalPromotionGateReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo empirical comparative promotion gate"
    "DASHI.Governance.BoloBoloEmpiricalPromotionGateExact"
    "ValidatedBoloCoordinationAdvantage / ValidatedBoloCoordinationDisadvantage / ValidatedMeaningfulBoloCoordinationAdvantage / ValidatedMeaningfulBoloCoordinationDisadvantage"
    "separates target-qualified robust bound classifications from validated comparative coordination claims by requiring frozen estimand/measurement definitions, documentary audit, sensitivity analysis and prospective validation or replication; a stronger meaningful tier additionally freezes a minimum practical margin before target outcomes and requires conservative bounds to clear it, symmetrically for advantage and disadvantage"
    "validated coordination advantage still creates neither political legitimacy nor ecological viability or universal optimality, while a validated disadvantage applies only to the tested model/context rather than refuting every possible bolo variant"
    "agda -i . DASHI/Governance/BoloBoloEmpiricalPromotionGateRegression.agda"
