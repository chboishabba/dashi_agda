module DASHI.Governance.BoloBoloCounterfactualEvaluationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Source
import DASHI.Governance.BoloBoloDerivedScaleEnvelopeExact as Scale
import DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact as Locality
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust
import DASHI.Governance.BoloBoloOccupyCalibrationBridgeExact as Calibration
import DASHI.Governance.BoloBoloCalibrationTransferExact as Transfer
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment

------------------------------------------------------------------------
-- PROJECT-LEVEL BOLO'BOLO COUNTERFACTUAL EVALUATION.
--
-- The programme is now explicitly layered:
--   source design
--   -> derived structural/locality model
--   -> exact + robust counterfactual cost theorems
--   -> historical calibration / transfer qualification
--   -> direct same-context flat-vs-nested experiment
--   -> only then empirical comparative promotion.
------------------------------------------------------------------------

record BoloCounterfactualEvaluation : Set where
  constructor boloCounterfactualEvaluation
  field
    sourceDesign : Source.BoloBoloPrimarySourceAtlas
    derivedScaleEnvelope : Scale.DerivedScaleEnvelope
    nestedDesign : Comparison.BoloNestedArchitectureDesign
    robustNestedBoundTargets : Robust.NestedCostBoundTargets
    calibrationPacket : Calibration.BoloOccupyCalibrationPacket
    calibrationObligations : Calibration.BoloComparisonCalibrationObligations
    directExperimentTermMapping : Experiment.CounterfactualTermMappingPlan

open BoloCounterfactualEvaluation public

canonicalBoloCounterfactualEvaluation : BoloCounterfactualEvaluation
canonicalBoloCounterfactualEvaluation =
  boloCounterfactualEvaluation
    Source.canonicalBoloBoloPrimarySourceAtlas
    Scale.canonicalDerivedScaleEnvelope
    Comparison.canonicalBoloNestedArchitectureDesign
    Robust.canonicalNestedCostBoundTargets
    Calibration.canonicalBoloOccupyCalibrationPacket
    Calibration.canonicalCalibrationObligations
    Experiment.canonicalCounterfactualTermMappingPlan

record BoloEvaluationBoundary : Set where
  constructor boloEvaluationBoundary
  field
    nestedSourceDesignPaid : Bool
    derivedScaleEnvelopePaid : Bool
    structuralLocalityContractionPaid : Bool
    conditionalFederationWinTheoremPaid : Bool
    robustPartialIdentificationTheoremPaid : Bool
    occupyCalibrationFrontierPaid : Bool
    crossContextTransferFirewallPaid : Bool
    directFlatVersusNestedExperimentDesignPaid : Bool

    empiricalCostTermsIdentified : Bool
    targetQualifiedCostBoundsPaid : Bool
    robustTargetCoordinationWinPaid : Bool
    removalPaysOverheadEmpiricallyPaid : Bool
    directFlatVersusNestedExperimentRun : Bool
    prospectiveHoldoutSpendable : Bool
    prospectiveHoldoutValidationPaid : Bool

    actualPoliticalLegitimacyEstablished : Bool
    concreteEcologicalViabilityEstablished : Bool
    concreteResourceBasicNeedsViabilityEstablished : Bool
    empiricalComparativeSuperiorityEstablished : Bool

    structuralTheoremAutomaticallyBecomesPoliticalRecommendation : Bool
    sourceArchitectureAutomaticallyBecomesEmpiricalOptimum : Bool
    occupyFailureAutomaticallyProvesBoloSuccess : Bool
    occupyBoundsAutomaticallyTransferToBolo : Bool
    robustCoordinationWinAutomaticallyImpliesTotalPoliticalSuccess : Bool

open BoloEvaluationBoundary public

canonicalBoloEvaluationBoundary : BoloEvaluationBoundary
canonicalBoloEvaluationBoundary =
  boloEvaluationBoundary
    true true true true true true true true
    false false false false false false false
    false false false false
    false false false false false

data BoloResearchLane : Set where
  sourceArchitectureLane : BoloResearchLane
  derivedScaleScenarioLane : BoloResearchLane
  localityTopologyLane : BoloResearchLane
  exactCounterfactualCostLane : BoloResearchLane
  robustPartialIdentificationLane : BoloResearchLane
  occupyCalibrationLane : BoloResearchLane
  crossContextTransferLane : BoloResearchLane
  directPairedExperimentLane : BoloResearchLane
  legitimacyLane : BoloResearchLane
  ecologicalResourceViabilityLane : BoloResearchLane
  comparativeValidationLane : BoloResearchLane

record BoloResearchLaneStatus : Set where
  constructor boloResearchLaneStatus
  field
    lane : BoloResearchLane
    structuralSurfacePresent : Bool
    empiricalPromotionPaid : Bool

open BoloResearchLaneStatus public

canonicalLaneStatuses : List BoloResearchLaneStatus
canonicalLaneStatuses =
  boloResearchLaneStatus sourceArchitectureLane true false
  ∷ boloResearchLaneStatus derivedScaleScenarioLane true false
  ∷ boloResearchLaneStatus localityTopologyLane true false
  ∷ boloResearchLaneStatus exactCounterfactualCostLane true false
  ∷ boloResearchLaneStatus robustPartialIdentificationLane true false
  ∷ boloResearchLaneStatus occupyCalibrationLane true false
  ∷ boloResearchLaneStatus crossContextTransferLane true false
  ∷ boloResearchLaneStatus directPairedExperimentLane true false
  ∷ boloResearchLaneStatus legitimacyLane true false
  ∷ boloResearchLaneStatus ecologicalResourceViabilityLane true false
  ∷ boloResearchLaneStatus comparativeValidationLane true false
  ∷ []

------------------------------------------------------------------------
-- Interpretation of the max-cut.
--
-- Structurally paid:
--   * source-bounded nested architecture and arithmetic scenarios;
--   * local-vs-global participation contraction under explicit witnesses;
--   * exact, linear, multi-level and robust interval win/loss criteria;
--   * an explicit Occupy calibration surface;
--   * a firewall for transporting historical bounds into a bolo target;
--   * a same-context paired experiment design that can directly estimate the
--     structural contrast without requiring unqualified historical transport.
--
-- Empirically unpaid:
--   * target-qualified bounds on removed coupling and all nested overheads;
--   * a robust target win/loss classification;
--   * the direct experiment itself;
--   * prospective validation and all broader legitimacy/viability claims.
------------------------------------------------------------------------

canonicalBoloCounterfactualEvaluationReceipt : GenericReceipt.GenericReceipt
canonicalBoloCounterfactualEvaluationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo counterfactual evaluation max-cut"
    "DASHI.Governance.BoloBoloCounterfactualEvaluationExact"
    "canonicalBoloEvaluationBoundary / canonicalLaneStatuses"
    "re-centres the governance programme on bolo'bolo as a candidate nested structural solution and closes the structural comparison surface through source-bounded design, derived scale scenarios, strict locality contraction, exact/linear/multi-level federation-win theorems, robust interval win/loss criteria, explicit Occupy calibration sockets, cross-context transfer qualification and a direct same-context flat-vs-nested experiment design"
    "no target-qualified cost bounds or direct experiment outcomes presently instantiate the robust or exact win conditions; Occupy bounds cannot transfer automatically, the protected historical holdout remains blocked by its development gate, and legitimacy, ecological/resource/basic-needs viability and comparative political superiority remain separate unpaid claims"
    "agda -i . DASHI/Governance/BoloBoloCounterfactualEvaluationRegression.agda"
