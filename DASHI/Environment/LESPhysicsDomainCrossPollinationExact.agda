module DASHI.Environment.LESPhysicsDomainCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as ReductionCanonical
import DASHI.Core.ConsumerRelativeReductionSearchExact as ReductionSearch
import DASHI.Core.RobustInterventionAcrossHypothesesExact as RobustIntervention
import DASHI.Biology.Physical.C3Cube27ConsumerReductionAdapterExact as C3Reduction
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESConsumerRelativeMechanismReductionExact as LESReduction
import DASHI.Environment.LESAdaptiveSPACModelSearchExact as AdaptiveSPAC
import DASHI.Environment.LESModelFibreRobustInterventionExact as FibreIntervention
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESBioelectricGaugeChemistryExact as Bioelectric
import DASHI.Environment.LESEnvironmentSIQuantityBridgeExact as EnvironmentSI
import DASHI.Environment.LESPhysicalProcessSourceRegistryExact as Sources
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoilFungal
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as SoilBio
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as PlantHydraulics
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Constitutive
import DASHI.Environment.FiniteSPACCalibrationExperimentExact as FiniteExperiment
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

data PhysicsReuseLane : Set where
  fluidMechanicsLane gaugeElectromagneticLane reactionTransportLane
  bioelectricElectrochemicalLane rootSoilFungalPhysiologyLane
  soilBiogeochemistryLane plantHydraulicAtmosphereCarbonLane
  soilPlantAtmosphereContinuumLane constitutiveSPACCalibrationLane
  consumerRelativeReductionLane activeExperimentDesignLane
  : PhysicsReuseLane

record PhysicsToDomainWeld : Set where
  constructor physicsToDomainWeld
  field
    lane : PhysicsReuseLane
    physicsOwner domainOwner sameCarrierOrReductionReference : String
    siQuantityReference constitutiveReference boundaryGeometryReference : String
    scaleRegimeReference validationReference : String
open PhysicsToDomainWeld public

record MechanisticDomainRealization : Set₁ where
  constructor mechanisticDomainRealization
  field
    mechanism : Basis.DomainMechanismSocket
    physicsWelds : List PhysicsToDomainWeld
    discrepancyModelReference experimentDesignReference : String
    identifiabilityReference heldOutValidationReference : String
open MechanisticDomainRealization public

stage7TargetObligations : List Robust.RobustnessObligation
stage7TargetObligations = Basis.stage7Obligations

siQuantityArchitectureOwner : String
siQuantityArchitectureOwner = "DASHI.Physics.Units.SI; BIPM DOI 10.59161/AUEZ1291"

environmentSIBridgeOwner : String
environmentSIBridgeOwner = "DASHI.Environment.LESEnvironmentSIQuantityBridgeExact"

physicalProcessSourceRegistryOwner : String
physicalProcessSourceRegistryOwner = "DASHI.Environment.LESPhysicalProcessSourceRegistryExact"

consumerRelativeReductionOwner : String
consumerRelativeReductionOwner = "DASHI.Core.ConsumerRelativeReductionKernelExact"

consumerRelativeReductionCanonicalOwner : String
consumerRelativeReductionCanonicalOwner = "DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact"

consumerRelativeReductionSearchOwner : String
consumerRelativeReductionSearchOwner = "DASHI.Core.ConsumerRelativeReductionSearchExact"

lesReductionAdapterOwner : String
lesReductionAdapterOwner = "DASHI.Environment.LESConsumerRelativeMechanismReductionExact"

adaptiveSPACModelSearchOwner : String
adaptiveSPACModelSearchOwner = "DASHI.Environment.LESAdaptiveSPACModelSearchExact"

modelFibreRobustInterventionOwner : String
modelFibreRobustInterventionOwner = "DASHI.Environment.LESModelFibreRobustInterventionExact"

finiteSPACExperimentOwner : String
finiteSPACExperimentOwner = "DASHI.Environment.FiniteSPACCalibrationExperimentExact"

u1Owner : String
u1Owner = "DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact"

pnpOwner : String
pnpOwner = "DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact; DOI 10.3390/electrochem2020014"

rootSoilFungalOwner : String
rootSoilFungalOwner = "DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact; DOI 10.1023/A:1026439226716 + 10.1104/pp.114.246124 + 10.1146/annurev-arplant-042110-103846"

soilBiogeochemistryOwner : String
soilBiogeochemistryOwner = "DASHI.Environment.SoilBiogeochemistryProcessNetworkExact; DOI 10.1016/j.soilbio.2009.02.031"

plantHydraulicOwner : String
plantHydraulicOwner = "DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact; DOI 10.1007/978-3-662-04931-0 + 10.1007/BF00386231 + 10.1111/pce.12823"

spacOwner : String
spacOwner = "DASHI.Environment.SoilPlantAtmosphereContinuumExact; DOI 10.2134/agronj2003.1362"

constitutiveCalibrationOwner : String
constitutiveCalibrationOwner = "DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact; DOI 10.1063/1.1745010 + 10.1029/WR012i003p00513 + 10.2136/sssaj1980.03615995004400050002x + 10.1111/j.1365-2486.2010.02375.x"

siVoltageDimension : SI.Dimension
siVoltageDimension = SI.Voltage

environmentWaterDimension : SI.Dimension
environmentWaterDimension = EnvironmentSI.dimension EnvironmentSI.waterLitresSI

u1BoundaryImported : EM.U1ElectromagneticBoundary
u1BoundaryImported = EM.canonicalU1ElectromagneticBoundary

pnpBoundaryImported : PNP.PNPElectrodiffusionBoundary
pnpBoundaryImported = PNP.canonicalPNPElectrodiffusionBoundary

sourceAttributionBoundaryImported : Sources.LESPhysicalProcessAttributionBoundary
sourceAttributionBoundaryImported = Sources.canonicalLESPhysicalProcessAttributionBoundary

rootSoilFungalBoundaryImported : RootSoilFungal.RootSoilFungalPhysiologyBoundary
rootSoilFungalBoundaryImported = RootSoilFungal.canonicalRootSoilFungalPhysiologyBoundary

soilBiogeochemistryBoundaryImported : SoilBio.SoilBiogeochemistryBoundary
soilBiogeochemistryBoundaryImported = SoilBio.canonicalSoilBiogeochemistryBoundary

plantHydraulicBoundaryImported : PlantHydraulics.PlantHydraulicAtmosphereCarbonBoundary
plantHydraulicBoundaryImported = PlantHydraulics.canonicalPlantHydraulicAtmosphereCarbonBoundary

spacBoundaryImported : SPAC.SPACBoundary
spacBoundaryImported = SPAC.canonicalSPACBoundary

constitutiveBoundaryImported : Constitutive.ConstitutiveHydrologyPlantBoundary
constitutiveBoundaryImported = Constitutive.canonicalConstitutiveHydrologyPlantBoundary

consumerReductionBoundaryImported : LESReduction.LESConsumerReductionBoundary
consumerReductionBoundaryImported = LESReduction.canonicalLESConsumerReductionBoundary

c3ReductionBoundaryImported : C3Reduction.C3Cube27ReductionBoundary
c3ReductionBoundaryImported = C3Reduction.canonicalC3Cube27ReductionBoundary

finiteExperimentBoundaryImported : FiniteExperiment.FiniteSPACExperimentBoundary
finiteExperimentBoundaryImported = FiniteExperiment.canonicalFiniteSPACExperimentBoundary

record LESPhysicsCrossPollinationCutset : Set where
  constructor lesPhysicsCrossPollinationCutset
  field
    navierStokesLaneReferenced certifiedSpatialTransportReferenced : Bool
    reactionTransportWeldTyped bioelectricChemistryLaneReferenced : Bool
    suNGaugeLaneReferencedWithBoundary canonicalSIUnitsOwnerPresent : Bool
    environmentalPhysicalUnitsWeldedToSI independentU1ApplicationOwnerPresent : Bool
    pnpElectrodiffusionOwnerPresent bioelectricPNPWeldTyped : Bool
    rootSoilFungalIonWaterArchitecturePresent rootSoilSameSpeciesWeldTyped : Bool
    mycorrhizalExtensionTyped soilCarbonNitrogenProcessArchitecturePresent : Bool
    soilPlantFungalBiogeochemistryWeldTyped plantHydraulicAtmosphereCarbonArchitecturePresent : Bool
    wholePlantSameStateWeldTyped atmosphereWindLeafBoundaryWeldTyped : Bool
    soilPlantAtmosphereContinuumArchitecturePresent spacBiogeochemistryFeedbackWeldTyped : Bool
    typedPhysicalProcessSourceRegistryPresent richardsPorousFlowReceiptTyped : Bool
    soilRetentionConductivityCalibrationTyped xylemConstitutiveCalibrationTyped : Bool
    stomatalPhotosynthesisCalibrationTyped constitutiveSPACCommonStateTyped : Bool

    reusableConsumerRelativeReductionKernelPresent : Bool
    exactResidualReopeningLayerPresent : Bool
    optionalSymmetryCompatibilityLayerPresent : Bool
    c3Cube27OptionalSymmetryAdapterPresent : Bool
    activeExperimentDiscriminatorTyped : Bool
    predictionEnvelopeMeasurementQuestionTyped : Bool
    onlineAssimilationFibreTyped : Bool
    mechanisticEquifinalityWitnessTyped : Bool
    controlTraceConsumerSafetyTyped : Bool
    historyHysteresisFutureWitnessTyped : Bool
    multifidelityEscalationWitnessTyped : Bool
    spatialScaleSafeAggregationTyped : Bool
    finiteSPACExperimentCarrierTyped : Bool

    applicationFluidReductionStillNeedsDomainReceipt : Bool
    applicationMaxwellConstitutiveReceiptsStillNeeded : Bool
    applicationPNPParametersAndBoundaryDataStillNeeded : Bool
    plantFluidPhysiologyWeldStillNeeded : Bool
    plantHydraulicParameterisationStillNeeded : Bool
    fungalSoilIonExchangeWeldStillNeeded : Bool
    soilBiogeochemistryParameterisationStillNeeded : Bool
    soilHydraulicConstitutiveReceiptStillNeeded : Bool
    atmosphereHydrologyConstitutiveWeldsStillNeeded : Bool
    actualFiniteSPACDatasetStillNeeded : Bool
    stage7ValidationStillNeeded : Bool
open LESPhysicsCrossPollinationCutset public

canonicalLESPhysicsCrossPollinationCutset : LESPhysicsCrossPollinationCutset
canonicalLESPhysicsCrossPollinationCutset =
  lesPhysicsCrossPollinationCutset
    true true true true true true true true true true
    true true true true true true true true true true
    true true true true true true
    true true true true true true true true true true true true true
    true true true false true true true false true true true

------------------------------------------------------------------------
-- New reduction-search / actionability cut.  Kept separate from the older
-- physical cutset so the theorem surface can evolve without destabilising its
-- constructor arity.
------------------------------------------------------------------------

record LESReductionSearchCrossPollinationCutset : Set where
  constructor lesReductionSearchCrossPollinationCutset
  field
    certifiedROMMapsToCanonicalFutureEquivalence : Bool
    candidateFutureCounterexampleRefutesSafety : Bool
    measurementDiscriminatorReusesActiveInformation : Bool
    symmetryOrbitCanBeProvedConsumerInvisible : Bool
    visibleSymmetryCannotBeSilentlyQuotiented : Bool
    reductionCandidatesUseReopenableHypothesisStatus : Bool
    deferredCandidateIsNotRefuted : Bool
    adaptiveSPACPortfolioTyped : Bool
    bucketToRichardsCounterexampleEscalationTyped : Bool
    richardsToSPACCounterexampleEscalationTyped : Bool
    spacToElectroBiogeochemicalEscalationTyped : Bool
    evidenceFibreRobustInterventionTyped : Bool
    evidenceRefinementPreservesExistingRobustControl : Bool
    measurementCanUnlockControlAfterHypothesisRefinement : Bool

open LESReductionSearchCrossPollinationCutset public

canonicalLESReductionSearchCrossPollinationCutset :
  LESReductionSearchCrossPollinationCutset
canonicalLESReductionSearchCrossPollinationCutset =
  lesReductionSearchCrossPollinationCutset
    true true true true true true true
    true true true true true true true

reductionCanonicalBoundaryImported :
  ReductionCanonical.ConsumerReductionCanonicalBridgeBoundary
reductionCanonicalBoundaryImported =
  ReductionCanonical.canonicalConsumerReductionCanonicalBridgeBoundary

reductionSearchBoundaryImported : ReductionSearch.ReductionSearchBoundary
reductionSearchBoundaryImported = ReductionSearch.canonicalReductionSearchBoundary

adaptiveSPACBoundaryImported : AdaptiveSPAC.LESAdaptiveSPACModelSearchBoundary
adaptiveSPACBoundaryImported = AdaptiveSPAC.canonicalLESAdaptiveSPACModelSearchBoundary

robustInterventionBoundaryImported : RobustIntervention.RobustInterventionBoundary
robustInterventionBoundaryImported =
  RobustIntervention.canonicalRobustInterventionBoundary

modelFibreInterventionBoundaryImported :
  FibreIntervention.LESModelFibreInterventionBoundary
modelFibreInterventionBoundaryImported =
  FibreIntervention.canonicalLESModelFibreInterventionBoundary

record LESPhysicsCrossPollinationBoundary : Set where
  constructor lesPhysicsCrossPollinationBoundary
  field
    physicalTheoremOwnerIsApplicationModel : Bool
    physicalTheoremOwnerIsApplicationModelIsFalse : physicalTheoremOwnerIsApplicationModel ≡ false
    sharedMathematicalStructureIsSharedEmpiricalMechanism : Bool
    sharedMathematicalStructureIsSharedEmpiricalMechanismIsFalse : sharedMathematicalStructureIsSharedEmpiricalMechanism ≡ false
    sameObjectIdentificationMayReplaceDuplicateApplicationProof : Bool
    sameObjectIdentificationMayReplaceDuplicateApplicationProofIsTrue : sameObjectIdentificationMayReplaceDuplicateApplicationProof ≡ true
    reductionReceiptStillNeedsRegimeValidation : Bool
    reductionReceiptStillNeedsRegimeValidationIsTrue : reductionReceiptStillNeedsRegimeValidation ≡ true
    siDimensionTypingReplacesConstitutivePhysics : Bool
    siDimensionTypingReplacesConstitutivePhysicsIsFalse : siDimensionTypingReplacesConstitutivePhysics ≡ false
    genericPNPReceiptIsUniversalPlantFungalNeuralModel : Bool
    genericPNPReceiptIsUniversalPlantFungalNeuralModelIsFalse : genericPNPReceiptIsUniversalPlantFungalNeuralModel ≡ false
    rootSoilFungalArchitectureIsUniversalParameterisation : Bool
    rootSoilFungalArchitectureIsUniversalParameterisationIsFalse : rootSoilFungalArchitectureIsUniversalParameterisation ≡ false
    soilCNProcessGrammarIsUniversalSoilModel : Bool
    soilCNProcessGrammarIsUniversalSoilModelIsFalse : soilCNProcessGrammarIsUniversalSoilModel ≡ false
    wholePlantHydraulicWeldIsUniversalCropModel : Bool
    wholePlantHydraulicWeldIsUniversalCropModelIsFalse : wholePlantHydraulicWeldIsUniversalCropModel ≡ false
    spacWeldEliminatesStorageAndHysteresis : Bool
    spacWeldEliminatesStorageAndHysteresisIsFalse : spacWeldEliminatesStorageAndHysteresis ≡ false
    typedSourceRegistryPromotesExternalClaimsToProof : Bool
    typedSourceRegistryPromotesExternalClaimsToProofIsFalse : typedSourceRegistryPromotesExternalClaimsToProof ≡ false
    fittedConstitutiveCalibrationIsHeldOutValidation : Bool
    fittedConstitutiveCalibrationIsHeldOutValidationIsFalse : fittedConstitutiveCalibrationIsHeldOutValidation ≡ false
    reductionSafetyIsLowReconstructionError : Bool
    reductionSafetyIsLowReconstructionErrorIsFalse : reductionSafetyIsLowReconstructionError ≡ false
    symmetryIsRequiredForEveryUsefulReduction : Bool
    symmetryIsRequiredForEveryUsefulReductionIsFalse : symmetryIsRequiredForEveryUsefulReduction ≡ false
    numbers369Or27EstablishPhysicalMechanism : Bool
    numbers369Or27EstablishPhysicalMechanismIsFalse : numbers369Or27EstablishPhysicalMechanism ≡ false

canonicalLESPhysicsCrossPollinationBoundary : LESPhysicsCrossPollinationBoundary
canonicalLESPhysicsCrossPollinationBoundary =
  lesPhysicsCrossPollinationBoundary
    false refl false refl true refl true refl false refl false refl
    false refl false refl false refl false refl false refl false refl
    false refl false refl false refl
