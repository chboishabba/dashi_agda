module DASHI.Environment.LESPhysicsDomainCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESBioelectricGaugeChemistryExact as Bioelectric
import DASHI.Environment.LESEnvironmentSIQuantityBridgeExact as EnvironmentSI
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- LES PHYSICS -> DOMAIN BIDI ASSEMBLY
------------------------------------------------------------------------

data PhysicsReuseLane : Set where
  fluidMechanicsLane
  gaugeElectromagneticLane
  reactionTransportLane
  bioelectricElectrochemicalLane
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

siVoltageDimension : SI.Dimension
siVoltageDimension = SI.Voltage

environmentWaterDimension : SI.Dimension
environmentWaterDimension = EnvironmentSI.dimension EnvironmentSI.waterLitresSI

record LESPhysicsCrossPollinationCutset : Set where
  constructor lesPhysicsCrossPollinationCutset
  field
    navierStokesLaneReferenced : Bool
    certifiedSpatialTransportReferenced : Bool
    reactionTransportWeldTyped : Bool
    bioelectricChemistryLaneReferenced : Bool
    suNGaugeLaneReferencedWithBoundary : Bool
    electrochemicalFieldSocketTyped : Bool
    canonicalSIUnitsOwnerPresent : Bool
    environmentalPhysicalUnitsWeldedToSI : Bool

    applicationFluidReductionStillNeedsDomainReceipt : Bool
    quantitativeElectromagneticU1OwnerStillNeeded : Bool
    electrodiffusionMembraneMechanismStillNeeded : Bool
    plantFluidPhysiologyWeldStillNeeded : Bool
    atmosphereHydrologyConstitutiveWeldsStillNeeded : Bool
    stage7ValidationStillNeeded : Bool

open LESPhysicsCrossPollinationCutset public

canonicalLESPhysicsCrossPollinationCutset : LESPhysicsCrossPollinationCutset
canonicalLESPhysicsCrossPollinationCutset =
  lesPhysicsCrossPollinationCutset
    true true true true true true true true
    true true true true true true

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

canonicalLESPhysicsCrossPollinationBoundary : LESPhysicsCrossPollinationBoundary
canonicalLESPhysicsCrossPollinationBoundary =
  lesPhysicsCrossPollinationBoundary false refl false refl true refl true refl false refl
