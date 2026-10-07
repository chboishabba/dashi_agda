module DASHI.Governance.BoloBoloEmpiricalPromotionGateExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Bounds
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

canonicalBoloEmpiricalPromotionGateReceipt : GenericReceipt.GenericReceipt
canonicalBoloEmpiricalPromotionGateReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo empirical comparative promotion gate"
    "DASHI.Governance.BoloBoloEmpiricalPromotionGateExact"
    "ValidatedBoloCoordinationAdvantage / ValidatedBoloCoordinationDisadvantage / canonicalEmpiricalPromotionBoundary"
    "separates a target-qualified robust bound classification from a validated comparative coordination claim by requiring frozen estimand/measurement definitions, documentary audit, sensitivity analysis and prospective validation or replication; the same gate supports a validated robust-loss certificate that can falsify the claimed coordination advantage for the tested model/context"
    "validated coordination advantage still creates neither political legitimacy nor ecological viability or universal optimality, while a validated disadvantage applies only to the tested model/context rather than refuting every possible bolo variant"
    "agda -i . DASHI/Governance/BoloBoloEmpiricalPromotionGateRegression.agda"
