module DASHI.Governance.BoloBoloCalibrationTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Bounds

------------------------------------------------------------------------
-- CALIBRATION TRANSFER FIREWALL.
--
-- Occupy can calibrate mechanisms and measurement strategies, but a bound
-- estimated in an OWS / People's Library context is not definitionally a bound
-- on a future bolo/kana/tega system.  A target-facing certificate therefore
-- requires either direct target-context measurement or an explicit transport
-- justification carrying the relevant context/source-regime assumptions.
------------------------------------------------------------------------

data CalibrationContext : Set where
  occupyGeneralAssemblyContext : CalibrationContext
  peoplesLibraryWorkingGroupContext : CalibrationContext
  candidateBoloFederationContext : CalibrationContext
  otherGovernanceContext : CalibrationContext

data TargetEvidenceMode : Set where
  directTargetMeasurement : TargetEvidenceMode
  justifiedCrossContextTransport : TargetEvidenceMode

record TransportAssumptionSurface : Set where
  constructor transportAssumptionSurface
  field
    participantScaleControlled : Bool
    issueMixControlled : Bool
    decisionRuleControlled : Bool
    sourceRegimeControlled : Bool
    externalShockContextControlled : Bool
    facilitationTechnologyControlled : Bool
    measurementDefinitionInvariantOrMapped : Bool

open TransportAssumptionSurface public

record BoloTargetBoundEvidence
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor boloTargetBoundEvidence
  field
    targetBounds : Bounds.CostIntervalBounds model
    evidenceMode : TargetEvidenceMode
    evidenceOriginLabel : String
    assumptionSurface : TransportAssumptionSurface

    ContextQualification : Set
    contextQualificationWitness : ContextQualification

    DocumentaryQualification : Set
    documentaryQualificationWitness : DocumentaryQualification

open BoloTargetBoundEvidence public

------------------------------------------------------------------------
-- Promotion carrier.
--
-- This is still only a coordination-cost claim.  It deliberately does not
-- project to legitimacy, ecology, desirability, or total political success.
------------------------------------------------------------------------

record BoloRobustCoordinationWin
  (model : Comparison.CounterfactualCoordinationCostModel) : Set₁ where
  constructor boloRobustCoordinationWin
  field
    evidence : BoloTargetBoundEvidence model
    robustWinWitness : Bounds.RobustWin (targetBounds evidence)

open BoloRobustCoordinationWin public

boloRobustCoordinationWinImpliesStrictCostOrder :
  ∀ {model} →
  BoloRobustCoordinationWin model →
  Bounds.StrictOrderImprovement model
boloRobustCoordinationWinImpliesStrictCostOrder certificate =
  Bounds.robustWinImpliesStrictOrderImprovement
    (targetBounds (evidence certificate))
    (robustWinWitness certificate)

------------------------------------------------------------------------
-- Attribution / transfer boundary.
------------------------------------------------------------------------

record CalibrationTransferBoundary : Set where
  constructor calibrationTransferBoundary
  field
    occupyContextDefinitionallyEquivalentToBoloTarget : Bool
    crossContextParameterTransportRequiresWitness : Bool
    directTargetMeasurementMayDischargeTransferNeed : Bool
    sourceScaleNumbersAreTransferCoefficients : Bool
    robustOccupyClassificationAutomaticallyBecomesBoloClassification : Bool
    transferAssumptionsMustBeExposed : Bool
    sourceRegimeMustRemainVisible : Bool
    transportCanBeFalsifiedByTargetEvidence : Bool
    robustTargetCoordinationWinCreatesPoliticalRecommendation : Bool

open CalibrationTransferBoundary public

canonicalCalibrationTransferBoundary : CalibrationTransferBoundary
canonicalCalibrationTransferBoundary =
  calibrationTransferBoundary
    false
    true
    true
    false
    false
    true
    true
    true
    false

canonicalBoloCalibrationTransferReceipt : GenericReceipt.GenericReceipt
canonicalBoloCalibrationTransferReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy-to-bolo calibration transfer firewall"
    "DASHI.Governance.BoloBoloCalibrationTransferExact"
    "BoloTargetBoundEvidence / boloRobustCoordinationWinImpliesStrictCostOrder / canonicalCalibrationTransferBoundary"
    "requires target-facing cost bounds to be supported either by direct target-context measurement or by an explicit cross-context transport qualification carrying source-regime and contextual assumptions; once target-qualified bounds satisfy the robust-win separation, the existing bound theorem yields a strict coordination-cost ordering"
    "OWS and bolo contexts are not definitionally equivalent, p.m.'s scale numbers are not transport coefficients, an Occupy classification does not automatically become a bolo classification, and even a target-qualified robust coordination win is not by itself a political recommendation"
    "agda -i . DASHI/Governance/BoloBoloCalibrationTransferRegression.agda"
