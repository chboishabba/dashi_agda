module DASHI.Environment.LESPhysicsDomainCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESBioelectricGaugeChemistryExact as Bioelectric
import DASHI.Environment.LESEnvironmentSIQuantityBridgeExact as EnvironmentSI
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoilFungal
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as SoilBio
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as PlantHydraulics
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- LES PHYSICS -> DOMAIN BIDI ASSEMBLY
------------------------------------------------------------------------

data PhysicsReuseLane : Set where
  fluidMechanicsLane
  gaugeElectromagneticLane
  reactionTransportLane
  bioelectricElectrochemicalLane
  rootSoilFungalPhysiologyLane
  soilBiogeochemistryLane
  plantHydraulicAtmosphereCarbonLane
  soilPlantAtmosphereContinuumLane
  : PhysicsReuseLane

record PhysicsToDomainWeld : Set where
  constructor physicsToDomainWeld
  field
    lane : PhysicsReuseLane
    physicsOwner : String
    domainOwner : String
    sameCarrierOrReductionReference : String
    siQuantityReference : String
    constitutiveReference : String
    boundaryGeometryReference : String
    scaleRegimeReference : String
    validationReference : String

open PhysicsToDomainWeld public

record MechanisticDomainRealization : Set₁ where
  constructor mechanisticDomainRealization
  field
    mechanism : Basis.DomainMechanismSocket
    physicsWelds : List PhysicsToDomainWeld
    discrepancyModelReference : String
    experimentDesignReference : String
    identifiabilityReference : String
    heldOutValidationReference : String

open MechanisticDomainRealization public

stage7TargetObligations : List Robust.RobustnessObligation
stage7TargetObligations = Basis.stage7Obligations

siQuantityArchitectureOwner : String
siQuantityArchitectureOwner = "DASHI.Physics.Units.SI; BIPM DOI 10.59161/AUEZ1291"

environmentSIBridgeOwner : String
environmentSIBridgeOwner = "DASHI.Environment.LESEnvironmentSIQuantityBridgeExact"

u1Owner : String
u1Owner = "DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact"

pnpOwner : String
pnpOwner =
  "DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact; DOI 10.3390/electrochem2020014"

rootSoilFungalOwner : String
rootSoilFungalOwner =
  "DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact; DOI 10.1023/A:1026439226716 + 10.1104/pp.114.246124 + 10.1146/annurev-arplant-042110-103846"

soilBiogeochemistryOwner : String
soilBiogeochemistryOwner =
  "DASHI.Environment.SoilBiogeochemistryProcessNetworkExact; DOI 10.1016/j.soilbio.2009.02.031"

plantHydraulicOwner : String
plantHydraulicOwner =
  "DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact; DOI 10.1007/978-3-662-04931-0 + 10.1007/BF00386231 + 10.1111/pce.12823"

spacOwner : String
spacOwner =
  "DASHI.Environment.SoilPlantAtmosphereContinuumExact; DOI 10.2134/agronj2003.1362"

siVoltageDimension : SI.Dimension
siVoltageDimension = SI.Voltage

environmentWaterDimension : SI.Dimension
environmentWaterDimension = EnvironmentSI.dimension EnvironmentSI.waterLitresSI

u1BoundaryImported : EM.U1ElectromagneticBoundary
u1BoundaryImported = EM.canonicalU1ElectromagneticBoundary

pnpBoundaryImported : PNP.PNPElectrodiffusionBoundary
pnpBoundaryImported = PNP.canonicalPNPElectrodiffusionBoundary

rootSoilFungalBoundaryImported : RootSoilFungal.RootSoilFungalPhysiologyBoundary
rootSoilFungalBoundaryImported = RootSoilFungal.canonicalRootSoilFungalPhysiologyBoundary

soilBiogeochemistryBoundaryImported : SoilBio.SoilBiogeochemistryBoundary
soilBiogeochemistryBoundaryImported = SoilBio.canonicalSoilBiogeochemistryBoundary

plantHydraulicBoundaryImported : PlantHydraulics.PlantHydraulicAtmosphereCarbonBoundary
plantHydraulicBoundaryImported = PlantHydraulics.canonicalPlantHydraulicAtmosphereCarbonBoundary

spacBoundaryImported : SPAC.SPACBoundary
spacBoundaryImported = SPAC.canonicalSPACBoundary

record LESPhysicsCrossPollinationCutset : Set where
  constructor lesPhysicsCrossPollinationCutset
  field
    navierStokesLaneReferenced : Bool
    certifiedSpatialTransportReferenced : Bool
    reactionTransportWeldTyped : Bool
    bioelectricChemistryLaneReferenced : Bool
    suNGaugeLaneReferencedWithBoundary : Bool
    canonicalSIUnitsOwnerPresent : Bool
    environmentalPhysicalUnitsWeldedToSI : Bool
    independentU1ApplicationOwnerPresent : Bool
    pnpElectrodiffusionOwnerPresent : Bool
    bioelectricPNPWeldTyped : Bool
    rootSoilFungalIonWaterArchitecturePresent : Bool
    rootSoilSameSpeciesWeldTyped : Bool
    mycorrhizalExtensionTyped : Bool
    soilCarbonNitrogenProcessArchitecturePresent : Bool
    soilPlantFungalBiogeochemistryWeldTyped : Bool
    plantHydraulicAtmosphereCarbonArchitecturePresent : Bool
    wholePlantSameStateWeldTyped : Bool
    atmosphereWindLeafBoundaryWeldTyped : Bool
    soilPlantAtmosphereContinuumArchitecturePresent : Bool
    spacBiogeochemistryFeedbackWeldTyped : Bool

    applicationFluidReductionStillNeedsDomainReceipt : Bool
    applicationMaxwellConstitutiveReceiptsStillNeeded : Bool
    applicationPNPParametersAndBoundaryDataStillNeeded : Bool
    plantFluidPhysiologyWeldStillNeeded : Bool
    plantHydraulicParameterisationStillNeeded : Bool
    fungalSoilIonExchangeWeldStillNeeded : Bool
    soilBiogeochemistryParameterisationStillNeeded : Bool
    soilHydraulicConstitutiveReceiptStillNeeded : Bool
    atmosphereHydrologyConstitutiveWeldsStillNeeded : Bool
    stage7ValidationStillNeeded : Bool

open LESPhysicsCrossPollinationCutset public

canonicalLESPhysicsCrossPollinationCutset : LESPhysicsCrossPollinationCutset
canonicalLESPhysicsCrossPollinationCutset =
  lesPhysicsCrossPollinationCutset
    true true true true true true true true true true
    true true true true true true true true true true
    true true true false true true true true true true

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
    rootSoilFungalArchitectureIsUniversalParameterisationIsFalse :
      rootSoilFungalArchitectureIsUniversalParameterisation ≡ false
    soilCNProcessGrammarIsUniversalSoilModel : Bool
    soilCNProcessGrammarIsUniversalSoilModelIsFalse :
      soilCNProcessGrammarIsUniversalSoilModel ≡ false
    wholePlantHydraulicWeldIsUniversalCropModel : Bool
    wholePlantHydraulicWeldIsUniversalCropModelIsFalse :
      wholePlantHydraulicWeldIsUniversalCropModel ≡ false
    spacWeldEliminatesStorageAndHysteresis : Bool
    spacWeldEliminatesStorageAndHysteresisIsFalse :
      spacWeldEliminatesStorageAndHysteresis ≡ false

canonicalLESPhysicsCrossPollinationBoundary : LESPhysicsCrossPollinationBoundary
canonicalLESPhysicsCrossPollinationBoundary =
  lesPhysicsCrossPollinationBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
