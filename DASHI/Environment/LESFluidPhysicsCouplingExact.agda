module DASHI.Environment.LESFluidPhysicsCouplingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Environment.CertifiedSpatialTransportExact as Certified
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Papers.NavierStokes.TheoremInterfaceRound133Exact as NS
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- LES FLUID-PHYSICS COUPLING
------------------------------------------------------------------------

data FluidApplication : Set where
  surfaceWaterFlow
  groundwaterOrPorousFlow
  atmosphericWind
  dissolvedChemicalAdvection
  sedimentBearingFlow
  cellularOrTissueFluidTransport
  : FluidApplication

record SIFluidFieldSocket : Set₁ where
  constructor siFluidFieldSocket
  field
    FluidState : Set
    velocityScale : SI.DecimalScale
    pressureScale : SI.DecimalScale
    densityScale : SI.DecimalScale
    viscosityScale : SI.DecimalScale
    flowRateScale : SI.DecimalScale
    velocity : FluidState → SI.Quantity SI.Velocity velocityScale
    pressure : FluidState → SI.Quantity SI.Pressure pressureScale
    density : FluidState → SI.Quantity SI.Density densityScale
    dynamicViscosity : FluidState → SI.Quantity SI.DynamicViscosity viscosityScale
    volumetricFlowRate : FluidState → SI.Quantity SI.VolumetricFlowRate flowRateScale

open SIFluidFieldSocket public

record FluidReductionReceipt : Set₁ where
  constructor fluidReductionReceipt
  field
    application : FluidApplication
    fieldSocket : SIFluidFieldSocket
    navierStokesOwner : String
    applicationStateReference : String
    velocityPressureIdentification : String
    geometryAndBoundaryReference : String
    forcingReference : String
    constitutiveRegimeReference : String
    incompressibilityOrAlternativeRegimeReference : String
    scaleReductionReference : String
    validationReference : String

open FluidReductionReceipt public

record FluidTransportCoupling
    {Source Target : Spatial.SpatialNode}
    (transportWitness : Certified.CertifiedSourceToObservation Source Target)
    : Set₁ where
  constructor fluidTransportCoupling
  field
    reduction : FluidReductionReceipt
    transportMechanismMatchesApplication : String
    fluxOrVelocityToEdgeCapacityReference : String
    timingCompatibilityReference : String

open FluidTransportCoupling public

record ReactionTransportWeld
    {Source Target : Spatial.SpatialNode}
    (transportWitness : Certified.CertifiedSourceToObservation Source Target)
    : Set₁ where
  constructor reactionTransportWeld
  field
    chemicalTransition : Chemistry.Transition
    fluidCoupling : FluidTransportCoupling transportWitness
    concentrationCarrierReference : String
    diffusionCoefficientReference : String
    advectionReference : String
    reactionSourceSinkReference : String
    conservationReference : String
    commonSpaceTimeCarrierReference : String

open ReactionTransportWeld public

nsProofLaneReference : String
nsProofLaneReference = "DASHI.Papers.NavierStokes.TheoremInterfaceRound133Exact"

siFluidQuantityOwnerReference : String
siFluidQuantityOwnerReference = "DASHI.Physics.Units.SI; BIPM DOI 10.59161/AUEZ1291"

nsImportedClayPromotion : Bool
nsImportedClayPromotion = NS.round133PaperClayPromotion

nsImportedClayPromotionIsFalse : nsImportedClayPromotion ≡ false
nsImportedClayPromotionIsFalse = NS.round133PaperClayPromotionIsFalse

record LESFluidPhysicsBoundary : Set where
  constructor lesFluidPhysicsBoundary
  field
    transportPathIsNavierStokesSolution : Bool
    transportPathIsNavierStokesSolutionIsFalse : transportPathIsNavierStokesSolution ≡ false
    navierStokesLaneAutomaticallyValidatesHydrology : Bool
    navierStokesLaneAutomaticallyValidatesHydrologyIsFalse : navierStokesLaneAutomaticallyValidatesHydrology ≡ false
    groundwaterMustUseUnreducedIncompressibleNS : Bool
    groundwaterMustUseUnreducedIncompressibleNSIsFalse : groundwaterMustUseUnreducedIncompressibleNS ≡ false
    atmosphericWindIsIdenticalToClayNSProblem : Bool
    atmosphericWindIsIdenticalToClayNSProblemIsFalse : atmosphericWindIsIdenticalToClayNSProblem ≡ false
    chemistryTransitionPlusTransportPathProvesReactionTransportPDE : Bool
    chemistryTransitionPlusTransportPathProvesReactionTransportPDEIsFalse : chemistryTransitionPlusTransportPathProvesReactionTransportPDE ≡ false
    fluidSocketUsesCanonicalSIQuantities : Bool
    fluidSocketUsesCanonicalSIQuantitiesIsTrue : fluidSocketUsesCanonicalSIQuantities ≡ true
    cellularFluidUseRequiresApplicationReduction : Bool
    cellularFluidUseRequiresApplicationReductionIsTrue : cellularFluidUseRequiresApplicationReduction ≡ true

canonicalLESFluidPhysicsBoundary : LESFluidPhysicsBoundary
canonicalLESFluidPhysicsBoundary =
  lesFluidPhysicsBoundary false refl false refl false refl false refl false refl true refl true refl
