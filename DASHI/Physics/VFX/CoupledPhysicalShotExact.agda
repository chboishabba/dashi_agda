module DASHI.Physics.VFX.CoupledPhysicalShotExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- COUPLED PHYSICAL VFX SHOT
--
-- Purpose: one same-object carrier for a physically coupled VFX shot such as
-- a massive creature stepping onto/against a naval vessel while water, air,
-- structure and optional electromagnetic effects respond.
--
-- This is an orchestration/admission surface, not a new NS/YM theorem and not
-- a claim that any particular production solver is physically authoritative.
------------------------------------------------------------------------

record ShotIdentity : Set where
  constructor shot-identity
  field
    shotId : String
    timelineRevision : String
    geometryRevision : String
    materialRevision : String
    solverRevision : String

open ShotIdentity public

record RigidBodyCoordinate : Set where
  constructor rigid-body-coordinate
  field
    massDimension : SI.Dimension
    massDimensionIsSI : massDimension ≡ SI.Mass
    velocityDimension : SI.Dimension
    velocityDimensionIsSI : velocityDimension ≡ SI.Velocity
    accelerationDimension : SI.Dimension
    accelerationDimensionIsSI : accelerationDimension ≡ SI.Acceleration
    forceDimension : SI.Dimension
    forceDimensionIsSI : forceDimension ≡ SI.Force
    bodyStateArtifact : String

open RigidBodyCoordinate public

record FluidCoordinate : Set where
  constructor fluid-coordinate
  field
    densityDimension : SI.Dimension
    densityDimensionIsSI : densityDimension ≡ SI.Density
    viscosityDimension : SI.Dimension
    viscosityDimensionIsSI : viscosityDimension ≡ SI.DynamicViscosity
    pressureDimension : SI.Dimension
    pressureDimensionIsSI : pressureDimension ≡ SI.Pressure
    velocityDimension : SI.Dimension
    velocityDimensionIsSI : velocityDimension ≡ SI.Velocity
    freeSurfaceArtifact : String
    wakeArtifact : String
    navierStokesOwner : String
    numericalFluidMethod : String

open FluidCoordinate public

record AirCoordinate : Set where
  constructor air-coordinate
  field
    densityDimension : SI.Dimension
    densityDimensionIsSI : densityDimension ≡ SI.Density
    velocityDimension : SI.Dimension
    velocityDimensionIsSI : velocityDimension ≡ SI.Velocity
    pressureDimension : SI.Dimension
    pressureDimensionIsSI : pressureDimension ≡ SI.Pressure
    aerodynamicArtifact : String
    compressibilityModel : String

open AirCoordinate public

record StructuralCoordinate : Set where
  constructor structural-coordinate
  field
    forceDimension : SI.Dimension
    forceDimensionIsSI : forceDimension ≡ SI.Force
    pressureDimension : SI.Dimension
    pressureDimensionIsSI : pressureDimension ≡ SI.Pressure
    displacementArtifact : String
    contactArtifact : String
    constitutiveModel : String
    fractureOrPlasticityModel : String

open StructuralCoordinate public

record ElectromagneticCoordinate : Set where
  constructor electromagnetic-coordinate
  field
    enabled : Bool
    chargeDimension : SI.Dimension
    chargeDimensionIsSI : chargeDimension ≡ SI.Charge
    electricFieldDimension : SI.Dimension
    electricFieldDimensionIsSI : electricFieldDimension ≡ SI.ElectricField
    magneticFluxDensityDimension : SI.Dimension
    magneticFluxDensityDimensionIsSI : magneticFluxDensityDimension ≡ SI.MagneticFluxDensity
    maxwellOwner : String
    chargeGenerationMechanism : String
    fieldArtifact : String

open ElectromagneticCoordinate public

record CoupledPhysicalShot (id : ShotIdentity) : Set₁ where
  constructor coupled-physical-shot
  field
    creatureRigidBody : RigidBodyCoordinate
    vesselRigidBody : RigidBodyCoordinate
    seawater : FluidCoordinate
    atmosphere : AirCoordinate
    vesselStructure : StructuralCoordinate
    electromagnetic : ElectromagneticCoordinate

    creatureVesselContactSameTimeline : String
    vesselWaterBoundarySameGeometry : String
    creatureAirBoundarySameGeometry : String
    pressureLoadsAppliedToSameVesselState : String
    contactLoadsAppliedToSameVesselState : String
    momentumExchangeClosure : String
    energyExchangeAudit : String
    solverCouplingOrder : String
    substepPolicy : String

open CoupledPhysicalShot public

------------------------------------------------------------------------
-- Rendering is a consumer of the physical carrier, not the source of truth.
------------------------------------------------------------------------

record VFXRenderObservation {id : ShotIdentity} (shot : CoupledPhysicalShot id) : Set₁ where
  constructor vfx-render-observation
  field
    renderedFrameArtifact : String
    cameraModel : String
    motionBlurModel : String
    sprayFoamMistModel : String
    volumetricAtmosphereModel : String
    shadingModel : String
    renderRevision : String

open VFXRenderObservation public

record CoupledShotResiduals {id : ShotIdentity} (shot : CoupledPhysicalShot id) : Set₁ where
  constructor coupled-shot-residuals
  field
    momentumResidual : String
    energyResidual : String
    fluidBoundaryResidual : String
    contactResidual : String
    structuralResidual : String
    freeSurfaceResidual : String
    wakeResidual : String
    aerodynamicResidual : String
    electromagneticResidual : String
    temporalCouplingResidual : String
    visualContinuityResidual : String

open CoupledShotResiduals public

record CoupledShotAdmission {id : ShotIdentity} (shot : CoupledPhysicalShot id) : Set₁ where
  constructor coupled-shot-admission
  field
    sameObjectResiduals : CoupledShotResiduals shot
    declaredPhysicalTolerancePolicy : String
    declaredVisualTolerancePolicy : String
    calibrationEvidence : String
    numericalConvergenceEvidence : String
    artifactDigest : String
    heldOutReferenceOrNegativeControl : String

open CoupledShotAdmission public

------------------------------------------------------------------------
-- Cross-pollination map. These are source/owner references, not theorem
-- inhabitants. In particular, Clay-level NS/YM work is not required to render
-- a finite numerical shot, and a visually successful shot does not certify it.
------------------------------------------------------------------------

navierStokesReuseOwner : String
navierStokesReuseOwner = "DASHI.Papers.NavierStokes + DASHI.Physics.Closure NS owners; reuse only as fluid-analysis/formal-governance substrate"

maxwellReuseOwner : String
maxwellReuseOwner = "DASHI.Physics.Electromagnetism.Everything; ordinary production EM effects route through Maxwell-scale owners"

yangMillsBoundary : String
yangMillsBoundary = "Yang-Mills formal content may supply gauge-theory structure, but ordinary charged/static VFX effects are not promoted to a Clay YM computation"

siReuseOwner : String
siReuseOwner = "DASHI.Physics.Units.SI; BIPM SI DOI 10.59161/AUEZ1291"

------------------------------------------------------------------------
-- Non-promotion boundaries discovered by introspective inspection.
------------------------------------------------------------------------

data LooksRightProvesPhysics : Set where
looksRightDoesNotProvePhysics : LooksRightProvesPhysics → ⊥
looksRightDoesNotProvePhysics ()

data NavierStokesClayProofRequiredForFiniteVFXFluidSolve : Set where
nsClayProofNotRequiredForFiniteVFXFluidSolve :
  NavierStokesClayProofRequiredForFiniteVFXFluidSolve → ⊥
nsClayProofNotRequiredForFiniteVFXFluidSolve ()

data YangMillsClayProofRequiredForOrdinaryVFXElectromagnetism : Set where
yangMillsClayProofNotRequiredForOrdinaryVFXElectromagnetism :
  YangMillsClayProofRequiredForOrdinaryVFXElectromagnetism → ⊥
yangMillsClayProofNotRequiredForOrdinaryVFXElectromagnetism ()

data OptionalEMCoordinateMeansEMEffectIsMaterial : Set where
optionalEMDoesNotMeanMaterialEMEffect : OptionalEMCoordinateMeansEMEffectIsMaterial → ⊥
optionalEMDoesNotMeanMaterialEMEffect ()

data WakeProxyIsFullFreeSurfaceNS : Set where
wakeProxyIsNotFullFreeSurfaceNS : WakeProxyIsFullFreeSurfaceNS → ⊥
wakeProxyIsNotFullFreeSurfaceNS ()
