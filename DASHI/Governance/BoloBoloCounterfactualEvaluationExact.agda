module DASHI.Governance.BoloBoloCounterfactualEvaluationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Source
import DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact as Locality
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloOccupyCalibrationBridgeExact as Calibration

------------------------------------------------------------------------
-- BOLO'BOLO COUNTERFACTUAL EVALUATION CAPSTONE.
--
-- This owner answers the project-level question:
--   what is already proved structurally, what is only an empirical calibration
--   programme, and what would be required before saying the nested federation
--   outperforms a globally coupled consensus architecture?
------------------------------------------------------------------------

record BoloCounterfactualEvaluation : Set where
  constructor boloCounterfactualEvaluation
  field
    sourceDesign : Source.BoloBoloPrimarySourceAtlas
    nestedDesign : Comparison.BoloNestedArchitectureDesign
    calibrationPacket : Calibration.BoloOccupyCalibrationPacket
    calibrationObligations : Calibration.BoloComparisonCalibrationObligations

open BoloCounterfactualEvaluation public

canonicalBoloCounterfactualEvaluation : BoloCounterfactualEvaluation
canonicalBoloCounterfactualEvaluation =
  boloCounterfactualEvaluation
    Source.canonicalBoloBoloPrimarySourceAtlas
    Comparison.canonicalBoloNestedArchitectureDesign
    Calibration.canonicalBoloOccupyCalibrationPacket
    Calibration.canonicalCalibrationObligations

------------------------------------------------------------------------
-- Project-level promotion frontier.
------------------------------------------------------------------------

record BoloEvaluationBoundary : Set where
  constructor boloEvaluationBoundary
  field
    nestedSourceDesignPaid : Bool
    structuralLocalityContractionPaid : Bool
    conditionalFederationWinTheoremPaid : Bool
    occupyCalibrationFrontierPaid : Bool

    empiricalCostTermsIdentified : Bool
    removalPaysOverheadEmpiricallyPaid : Bool
    prospectiveHoldoutSpendable : Bool
    prospectiveHoldoutValidationPaid : Bool

    actualPoliticalLegitimacyEstablished : Bool
    concreteEcologicalViabilityEstablished : Bool
    concreteResourceBasicNeedsViabilityEstablished : Bool
    empiricalComparativeSuperiorityEstablished : Bool

    structuralTheoremAutomaticallyBecomesPoliticalRecommendation : Bool
    sourceArchitectureAutomaticallyBecomesEmpiricalOptimum : Bool
    occupyFailureAutomaticallyProvesBoloSuccess : Bool

open BoloEvaluationBoundary public

canonicalBoloEvaluationBoundary : BoloEvaluationBoundary
canonicalBoloEvaluationBoundary =
  boloEvaluationBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Research-program decomposition.
------------------------------------------------------------------------

data BoloResearchLane : Set where
  sourceArchitectureLane : BoloResearchLane
  localityTopologyLane : BoloResearchLane
  counterfactualCostLane : BoloResearchLane
  occupyCalibrationLane : BoloResearchLane
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
  ∷ boloResearchLaneStatus localityTopologyLane true false
  ∷ boloResearchLaneStatus counterfactualCostLane true false
  ∷ boloResearchLaneStatus occupyCalibrationLane true false
  ∷ boloResearchLaneStatus legitimacyLane true false
  ∷ boloResearchLaneStatus ecologicalResourceViabilityLane true false
  ∷ boloResearchLaneStatus comparativeValidationLane true false
  ∷ []

------------------------------------------------------------------------
-- Interpretation:
--
-- Paid structurally:
--   source-bounded nested design;
--   strict local-vs-global participation contraction under explicit witnesses;
--   exact conditional theorem that federation wins when removed global cost
--   exceeds introduced federation overhead by a positive margin;
--   evidence sockets/calibration obligations for Occupy.
--
-- Unpaid empirically:
--   identified costs/bounds sufficient to instantiate RemovalPaysOverhead;
--   held-out validation;
--   legitimacy, ecological/resource/basic-needs viability;
--   comparative superiority.
------------------------------------------------------------------------

canonicalBoloCounterfactualEvaluationReceipt : GenericReceipt.GenericReceipt
canonicalBoloCounterfactualEvaluationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo counterfactual evaluation max-cut"
    "DASHI.Governance.BoloBoloCounterfactualEvaluationExact"
    "canonicalBoloEvaluationBoundary / canonicalLaneStatuses"
    "re-centres the governance programme on bolo'bolo as a candidate nested structural solution: source-bounded nested design, conditional subsidiarity contraction, and a sharp federation-win theorem are paid structurally, while Occupy is retained as an empirical calibration/falsification lane for the theorem's cost terms"
    "no required cost term is yet empirically identified, RemovalPaysOverhead is not instantiated from evidence, the protected holdout is not spendable, and legitimacy, ecological/resource/basic-needs viability and comparative superiority remain separate unpaid claims"
    "agda -i . DASHI/Governance/BoloBoloCounterfactualEvaluationRegression.agda"
