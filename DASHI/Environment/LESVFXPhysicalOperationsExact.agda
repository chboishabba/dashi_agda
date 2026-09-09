module DASHI.Environment.LESVFXPhysicalOperationsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Laws.PhysicalLawAtlas as Laws
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- COMMON VFX / PHYSICALLY BASED SIMULATION OPERATION FAMILIES
--
-- These are operation classes and admission seams over the existing physical
-- law atlas.  They do not identify a graphics technique with the underlying
-- physical law, nor does visual plausibility certify physical correctness.
------------------------------------------------------------------------

data VFXOperation : Set where
  rigidBodyAdvance : VFXOperation
  contactDetection : VFXOperation
  contactConstraintSolve : VFXOperation
  impulseResponse : VFXOperation
  frictionResponse : VFXOperation
  deformableSolidAdvance : VFXOperation
  fractureOrDamageAdvance : VFXOperation
  fluidAdvance : VFXOperation
  freeSurfaceAdvance : VFXOperation
  sprayFoamBubbleEmission : VFXOperation
  aerosolOrParticleTransport : VFXOperation
  acousticPropagation : VFXOperation
  electromagneticFieldAdvance : VFXOperation
  chargeTransferOrRelaxation : VFXOperation
  thermalTransport : VFXOperation
  opticalTransport : VFXOperation
  volumetricScattering : VFXOperation
  proceduralOrLearnedSurrogate : VFXOperation

record VFXOperationAuthority : Set₁ where
  constructor vfx-operation-authority
  field
    operation : VFXOperation
    physicalLaw : Laws.CanonicalPhysicalLaw
    sourceReference : String
    numericalMethodReference : String
    validityRegimeReference : String
    calibrationReference : String
    heldOutValidationReference : String

open VFXOperationAuthority public

------------------------------------------------------------------------
-- SI-facing scene quantities.  These are sockets only; a numerical backend
-- still has to provide vector/tensor algebra and compatible decimal scaling.
------------------------------------------------------------------------

record SIImpactSceneSocket : Set₁ where
  constructor si-impact-scene-socket
  field
    BodyState FluidState FieldState : Set

    lengthScale massScale timeScale velocityScale accelerationScale : SI.DecimalScale
    forceScale pressureScale energyScale powerScale : SI.DecimalScale
    densityScale viscosityScale electricFieldScale magneticFieldScale : SI.DecimalScale

    characteristicLength : BodyState → SI.Quantity SI.Length lengthScale
    bodyMass : BodyState → SI.Quantity SI.Mass massScale
    bodySpeed : BodyState → SI.Quantity SI.Velocity velocityScale
    bodyAcceleration : BodyState → SI.Quantity SI.Acceleration accelerationScale
    contactForce : BodyState → SI.Quantity SI.Force forceScale
    impactEnergy : BodyState → SI.Quantity SI.Energy energyScale

    fluidPressure : FluidState → SI.Quantity SI.Pressure pressureScale
    fluidDensity : FluidState → SI.Quantity SI.Density densityScale
    dynamicViscosity : FluidState → SI.Quantity SI.DynamicViscosity viscosityScale
    fluidVelocity : FluidState → SI.Quantity SI.Velocity velocityScale

    electricField : FieldState → SI.Quantity SI.ElectricField electricFieldScale
    magneticField : FieldState → SI.Quantity SI.MagneticFluxDensity magneticFieldScale

open SIImpactSceneSocket public

------------------------------------------------------------------------
-- A simulation step may compose many operations but each seam is explicit.
------------------------------------------------------------------------

record VFXCoupledStep : Set₁ where
  constructor vfx-coupled-step
  field
    sceneSocket : SIImpactSceneSocket
    rigidBody : VFXOperationAuthority
    contact : VFXOperationAuthority
    structure : VFXOperationAuthority
    water : VFXOperationAuthority
    air : VFXOperationAuthority
    acoustics : VFXOperationAuthority
    electromagnetism : VFXOperationAuthority
    optics : VFXOperationAuthority

    commonSpaceTimeCarrierReference : String
    forceExchangeReference : String
    momentumExchangeReference : String
    energyExchangeReference : String
    massConservationReference : String
    chargeConservationReference : String
    numericalCouplingReference : String
    timeIntegrationReference : String
    residualReference : String

open VFXCoupledStep public

------------------------------------------------------------------------
-- Source/ownership notes for graphics algorithms.
------------------------------------------------------------------------

baraffWitkinReference : String
baraffWitkinReference =
  "Andrew Witkin and David Baraff, Physically Based Modeling: Principles and Practice, SIGGRAPH 1997 course notes; rigid-body, constrained dynamics and contact-method context; no DOI asserted"

stamStableFluidsReference : String
stamStableFluidsReference =
  "Jos Stam, Stable Fluids, SIGGRAPH 1999, DOI 10.1145/311535.311548; computer-graphics fluid numerical method authority, not a proof of exact Navier-Stokes solution"

mullerPBDReference : String
mullerPBDReference =
  "Matthias Muller, Bruno Heidelberger, Marcus Hennix, John Ratcliff, Position Based Dynamics, JVCIR 18(2), 2007, DOI 10.1016/j.jvcir.2007.01.005; position-based constraint technique authority, not constitutive-material authority"

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data VisuallyPlausibleImpliesPhysicallyAccurate : Set where
visuallyPlausibleDoesNotImplyPhysicallyAccurate : VisuallyPlausibleImpliesPhysicallyAccurate → ⊥
visuallyPlausibleDoesNotImplyPhysicallyAccurate ()

data PositionConstraintIsPhysicalContactLawByDefinition : Set where
positionConstraintIsNotPhysicalContactLawByDefinition : PositionConstraintIsPhysicalContactLawByDefinition → ⊥
positionConstraintIsNotPhysicalContactLawByDefinition ()

data StableFluidsIsExactNavierStokesSolution : Set where
stableFluidsIsNotExactNavierStokesSolution : StableFluidsIsExactNavierStokesSolution → ⊥
stableFluidsIsNotExactNavierStokesSolution ()

data ParticleEmitterIsContinuumTwoPhaseFlow : Set where
particleEmitterIsNotContinuumTwoPhaseFlow : ParticleEmitterIsContinuumTwoPhaseFlow → ⊥
particleEmitterIsNotContinuumTwoPhaseFlow ()
