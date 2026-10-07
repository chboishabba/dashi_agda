module DASHI.Governance.BoloBoloCounterfactualEvaluationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Source
import DASHI.Governance.BoloBoloDerivedScaleEnvelopeExact as Scale
import DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact as Locality
import DASHI.Governance.BoloBoloIncidenceCompressionExact as Compression
import DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeExact as CompressionBridge
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust
import DASHI.Governance.BoloBoloNestedCostBoundCompilerExact as ComponentCompiler
import DASHI.Governance.BoloBoloPracticalSignificanceExact as Significance
import DASHI.Governance.BoloBoloLinearCalibrationBoundCompilerExact as LinearCompiler
import DASHI.Governance.BoloBoloOccupyCalibrationBridgeExact as Calibration
import DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact as Comparators
import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Spokes
import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Polycentric
import DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact as ComparatorFrontier
import DASHI.Governance.BoloBoloCalibrationTransferExact as Transfer
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.BoloBoloEmpiricalPromotionGateExact as Promotion
import DASHI.Governance.BoloBoloModelClassRobustnessExact as ModelRobustness

------------------------------------------------------------------------
-- PROJECT-LEVEL BOLO'BOLO COUNTERFACTUAL EVALUATION.
--
-- The programme is explicitly layered:
--   p.m. source design
--   -> DASHI scale / topology / locality scenario
--   -> incidence-compression accounting
--   -> exact + robust counterfactual cost theorems
--   -> component/count/weight bound compilers
--   -> predeclared minimum meaningful margin
--   -> historical Occupy calibration
--   -> independent real-world nested/polycentric comparators
--   -> same-context OWS flat-to-Spokes interrupted transition
--   -> cross-context transfer qualification or direct target measurement
--   -> same-context flat-vs-nested experiment
--   -> sensitivity + prospective validation / replication
--   -> meaningful advantage/disadvantage across a predeclared model family
--   -> broader legitimacy / ecological / political claims remain separate.
------------------------------------------------------------------------

record BoloCounterfactualEvaluation : Set where
  constructor boloCounterfactualEvaluation
  field
    sourceDesign : Source.BoloBoloPrimarySourceAtlas
    derivedScaleEnvelope : Scale.DerivedScaleEnvelope
    nestedDesign : Comparison.BoloNestedArchitectureDesign
    incidenceCompressionBoundary : Compression.IncidenceCompressionBoundary
    incidenceCompressionCostBridgeBoundary : CompressionBridge.CompressionCostBridgeBoundary
    robustNestedBoundTargets : Robust.NestedCostBoundTargets
    componentBoundCompilerBoundary : ComponentCompiler.NestedCostBoundCompilerBoundary
    practicalSignificanceBoundary : Significance.PracticalSignificanceBoundary
    linearCalibrationCompilerBoundary : LinearCompiler.LinearCalibrationCompilerBoundary
    calibrationPacket : Calibration.BoloOccupyCalibrationPacket
    calibrationObligations : Calibration.BoloComparisonCalibrationObligations
    comparatorEvidenceBoundary : Comparators.ComparatorEvidenceBoundary
    spokesTransitionBoundary : Spokes.OWSSpokesTransitionBoundary
    polycentricEvidenceSynthesis : Polycentric.PolycentricEvidenceSynthesis
    comparatorPrimitiveFrontier : ComparatorFrontier.PrimitiveCalibrationFrontier
    comparatorAcquisitionRoadmap : ComparatorFrontier.ComparatorAcquisitionRoadmap
    comparatorCalibrationBoundary : ComparatorFrontier.ComparatorCalibrationBoundary
    transferBoundary : Transfer.CalibrationTransferBoundary
    directExperimentTermMapping : Experiment.CounterfactualTermMappingPlan
    empiricalPromotionBoundary : Promotion.EmpiricalPromotionBoundary
    meaningfulPromotionBoundary : Promotion.MeaningfulPromotionBoundary
    modelClassRobustnessBoundary : ModelRobustness.ModelClassRobustnessBoundary

open BoloCounterfactualEvaluation public

canonicalBoloCounterfactualEvaluation : BoloCounterfactualEvaluation
canonicalBoloCounterfactualEvaluation = record
  { sourceDesign = Source.canonicalBoloBoloPrimarySourceAtlas
  ; derivedScaleEnvelope = Scale.canonicalDerivedScaleEnvelope
  ; nestedDesign = Comparison.canonicalBoloNestedArchitectureDesign
  ; incidenceCompressionBoundary = Compression.canonicalIncidenceCompressionBoundary
  ; incidenceCompressionCostBridgeBoundary = CompressionBridge.canonicalCompressionCostBridgeBoundary
  ; robustNestedBoundTargets = Robust.canonicalNestedCostBoundTargets
  ; componentBoundCompilerBoundary = ComponentCompiler.canonicalNestedCostBoundCompilerBoundary
  ; practicalSignificanceBoundary = Significance.canonicalPracticalSignificanceBoundary
  ; linearCalibrationCompilerBoundary = LinearCompiler.canonicalLinearCalibrationCompilerBoundary
  ; calibrationPacket = Calibration.canonicalBoloOccupyCalibrationPacket
  ; calibrationObligations = Calibration.canonicalCalibrationObligations
  ; comparatorEvidenceBoundary = Comparators.canonicalComparatorEvidenceBoundary
  ; spokesTransitionBoundary = Spokes.canonicalOWSSpokesTransitionBoundary
  ; polycentricEvidenceSynthesis = Polycentric.canonicalPolycentricEvidenceSynthesis
  ; comparatorPrimitiveFrontier = ComparatorFrontier.canonicalPrimitiveCalibrationFrontier
  ; comparatorAcquisitionRoadmap = ComparatorFrontier.canonicalComparatorAcquisitionRoadmap
  ; comparatorCalibrationBoundary = ComparatorFrontier.canonicalComparatorCalibrationBoundary
  ; transferBoundary = Transfer.canonicalCalibrationTransferBoundary
  ; directExperimentTermMapping = Experiment.canonicalCounterfactualTermMappingPlan
  ; empiricalPromotionBoundary = Promotion.canonicalEmpiricalPromotionBoundary
  ; meaningfulPromotionBoundary = Promotion.canonicalMeaningfulPromotionBoundary
  ; modelClassRobustnessBoundary = ModelRobustness.canonicalModelClassRobustnessBoundary
  }

record BoloEvaluationBoundary : Set where
  constructor boloEvaluationBoundary
  field
    nestedSourceDesignPaid : Bool
    derivedScaleEnvelopePaid : Bool
    structuralLocalityContractionPaid : Bool
    incidenceCompressionScenarioPaid : Bool
    incidenceCompressionCostBridgePaid : Bool
    conditionalFederationWinTheoremPaid : Bool
    robustPartialIdentificationTheoremPaid : Bool
    componentwiseCostBoundCompilerPaid : Bool
    practicalSignificanceGatePaid : Bool
    linearCalibrationBoundCompilerPaid : Bool
    occupyCalibrationFrontierPaid : Bool
    realWorldComparatorAtlasPaid : Bool
    owsSpokesInterruptedTransitionPaid : Bool
    polycentricEvidenceSynthesisPaid : Bool
    comparatorCalibrationFrontierPaid : Bool
    crossContextTransferFirewallPaid : Bool
    directFlatVersusNestedExperimentDesignPaid : Bool
    validatedEmpiricalPromotionGatePaid : Bool
    meaningfulEmpiricalPromotionGatePaid : Bool
    modelClassRobustnessGatePaid : Bool

    empiricalCostTermsIdentified : Bool
    targetQualifiedCostBoundsPaid : Bool
    minimumMeaningfulThresholdTargetStudyPaid : Bool
    admissibleTargetModelFamilyPaid : Bool
    robustTargetCoordinationWinPaid : Bool
    removalPaysOverheadEmpiricallyPaid : Bool
    underlyingOWSSpokesMinutesMaterialised : Bool
    directFlatVersusNestedExperimentRun : Bool
    validatedCoordinationAdvantagePaid : Bool
    validatedCoordinationDisadvantagePaid : Bool
    validatedMeaningfulAdvantagePaid : Bool
    validatedMeaningfulDisadvantagePaid : Bool
    uniformModelFamilyAdvantagePaid : Bool
    uniformModelFamilyDisadvantagePaid : Bool
    prospectiveHoldoutSpendable : Bool
    prospectiveHoldoutValidationPaid : Bool

    actualPoliticalLegitimacyEstablished : Bool
    concreteEcologicalViabilityEstablished : Bool
    concreteResourceBasicNeedsViabilityEstablished : Bool
    empiricalComparativeSuperiorityEstablished : Bool

    structuralTheoremAutomaticallyBecomesPoliticalRecommendation : Bool
    sourceArchitectureAutomaticallyBecomesEmpiricalOptimum : Bool
    occupyFailureAutomaticallyProvesBoloSuccess : Bool
    comparatorSimilarityAutomaticallyProvesBoloSuccess : Bool
    occupyBoundsAutomaticallyTransferToBolo : Bool
    robustCoordinationWinAutomaticallyImpliesTotalPoliticalSuccess : Bool
    validatedCoordinationDisadvantageRefutesEveryPossibleBoloVariant : Bool
    oneFavouredCostModelEnoughForRobustRecommendation : Bool
    anyTinyStrictWinEnoughForMeaningfulRecommendation : Bool

open BoloEvaluationBoundary public

canonicalBoloEvaluationBoundary : BoloEvaluationBoundary
canonicalBoloEvaluationBoundary = record
  { nestedSourceDesignPaid = true
  ; derivedScaleEnvelopePaid = true
  ; structuralLocalityContractionPaid = true
  ; incidenceCompressionScenarioPaid = true
  ; incidenceCompressionCostBridgePaid = true
  ; conditionalFederationWinTheoremPaid = true
  ; robustPartialIdentificationTheoremPaid = true
  ; componentwiseCostBoundCompilerPaid = true
  ; practicalSignificanceGatePaid = true
  ; linearCalibrationBoundCompilerPaid = true
  ; occupyCalibrationFrontierPaid = true
  ; realWorldComparatorAtlasPaid = true
  ; owsSpokesInterruptedTransitionPaid = true
  ; polycentricEvidenceSynthesisPaid = true
  ; comparatorCalibrationFrontierPaid = true
  ; crossContextTransferFirewallPaid = true
  ; directFlatVersusNestedExperimentDesignPaid = true
  ; validatedEmpiricalPromotionGatePaid = true
  ; meaningfulEmpiricalPromotionGatePaid = true
  ; modelClassRobustnessGatePaid = true
  ; empiricalCostTermsIdentified = false
  ; targetQualifiedCostBoundsPaid = false
  ; minimumMeaningfulThresholdTargetStudyPaid = false
  ; admissibleTargetModelFamilyPaid = false
  ; robustTargetCoordinationWinPaid = false
  ; removalPaysOverheadEmpiricallyPaid = false
  ; underlyingOWSSpokesMinutesMaterialised = false
  ; directFlatVersusNestedExperimentRun = false
  ; validatedCoordinationAdvantagePaid = false
  ; validatedCoordinationDisadvantagePaid = false
  ; validatedMeaningfulAdvantagePaid = false
  ; validatedMeaningfulDisadvantagePaid = false
  ; uniformModelFamilyAdvantagePaid = false
  ; uniformModelFamilyDisadvantagePaid = false
  ; prospectiveHoldoutSpendable = false
  ; prospectiveHoldoutValidationPaid = false
  ; actualPoliticalLegitimacyEstablished = false
  ; concreteEcologicalViabilityEstablished = false
  ; concreteResourceBasicNeedsViabilityEstablished = false
  ; empiricalComparativeSuperiorityEstablished = false
  ; structuralTheoremAutomaticallyBecomesPoliticalRecommendation = false
  ; sourceArchitectureAutomaticallyBecomesEmpiricalOptimum = false
  ; occupyFailureAutomaticallyProvesBoloSuccess = false
  ; comparatorSimilarityAutomaticallyProvesBoloSuccess = false
  ; occupyBoundsAutomaticallyTransferToBolo = false
  ; robustCoordinationWinAutomaticallyImpliesTotalPoliticalSuccess = false
  ; validatedCoordinationDisadvantageRefutesEveryPossibleBoloVariant = false
  ; oneFavouredCostModelEnoughForRobustRecommendation = false
  ; anyTinyStrictWinEnoughForMeaningfulRecommendation = false
  }

data BoloResearchLane : Set where
  sourceArchitectureLane : BoloResearchLane
  derivedScaleScenarioLane : BoloResearchLane
  localityTopologyLane : BoloResearchLane
  incidenceCompressionLane : BoloResearchLane
  incidenceToCostBridgeLane : BoloResearchLane
  exactCounterfactualCostLane : BoloResearchLane
  robustPartialIdentificationLane : BoloResearchLane
  componentwiseBoundCompilerLane : BoloResearchLane
  practicalSignificanceLane : BoloResearchLane
  linearCalibrationCompilerLane : BoloResearchLane
  occupyCalibrationLane : BoloResearchLane
  realWorldComparatorLane : BoloResearchLane
  sameContextSpokesTransitionLane : BoloResearchLane
  polycentricEvidenceSynthesisLane : BoloResearchLane
  comparatorCalibrationFrontierLane : BoloResearchLane
  crossContextTransferLane : BoloResearchLane
  directPairedExperimentLane : BoloResearchLane
  validatedPromotionFalsificationLane : BoloResearchLane
  modelClassRobustnessLane : BoloResearchLane
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
  ∷ boloResearchLaneStatus incidenceCompressionLane true false
  ∷ boloResearchLaneStatus incidenceToCostBridgeLane true false
  ∷ boloResearchLaneStatus exactCounterfactualCostLane true false
  ∷ boloResearchLaneStatus robustPartialIdentificationLane true false
  ∷ boloResearchLaneStatus componentwiseBoundCompilerLane true false
  ∷ boloResearchLaneStatus practicalSignificanceLane true false
  ∷ boloResearchLaneStatus linearCalibrationCompilerLane true false
  ∷ boloResearchLaneStatus occupyCalibrationLane true false
  ∷ boloResearchLaneStatus realWorldComparatorLane true false
  ∷ boloResearchLaneStatus sameContextSpokesTransitionLane true false
  ∷ boloResearchLaneStatus polycentricEvidenceSynthesisLane true false
  ∷ boloResearchLaneStatus comparatorCalibrationFrontierLane true false
  ∷ boloResearchLaneStatus crossContextTransferLane true false
  ∷ boloResearchLaneStatus directPairedExperimentLane true false
  ∷ boloResearchLaneStatus validatedPromotionFalsificationLane true false
  ∷ boloResearchLaneStatus modelClassRobustnessLane true false
  ∷ boloResearchLaneStatus legitimacyLane true false
  ∷ boloResearchLaneStatus ecologicalResourceViabilityLane true false
  ∷ boloResearchLaneStatus comparativeValidationLane true false
  ∷ []

------------------------------------------------------------------------
-- Max-cut interpretation.
--
-- Real-world comparators now cover every mechanism class in the candidate
-- cost model, but they do not identify target cost coefficients.  The closest
-- historical transition is OWS GA -> Spokes Council; the available source
-- record is mixed and confounded, and the underlying Spokes minutes are still
-- an acquisition target.  The remaining chain is therefore evidential:
--
--   source architecture
--   -> topology/locality scenario
--   -> incidence reduction accounting
--   -> primitive count/weight bounds
--   -> compiled cost bounds
--   -> exact/robust comparison
--   -> predeclared meaningful margin
--   -> target qualification
--   -> direct or transported evidence
--   -> sensitivity + prospective validation
--   -> robustness across a predeclared admissible cost-model family
--   -> meaningful validated advantage/disadvantage.
------------------------------------------------------------------------

canonicalBoloCounterfactualEvaluationReceipt : GenericReceipt.GenericReceipt
canonicalBoloCounterfactualEvaluationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo counterfactual evaluation max-cut"
    "DASHI.Governance.BoloBoloCounterfactualEvaluationExact"
    "canonicalBoloEvaluationBoundary / canonicalLaneStatuses"
    "closes the source-written and methodological chain from p.m.'s nested design through topology/incidence accounting, exact and robust cost comparison, bound compilers, practical significance, Occupy calibration, independent real-world comparators, the mixed/confounded same-context OWS GA-to-Spokes transition, polycentric evidence synthesis, transfer qualification, direct trial design, validated promotion/falsification and predeclared model-family robustness"
    "all candidate mechanism classes now have real-world observable analogues, but target-qualified primitive cost/weight bounds remain unpaid; the underlying Spokes minutes are still an acquisition target and comparator similarity, institutional durability or cross-domain performance cannot substitute for direct target measurement or qualified transport"
    "agda -i . DASHI/Governance/BoloBoloCounterfactualEvaluationRegression.agda"
