module DASHI.Environment.LESFluidPhysicsCouplingExact where

open import DASHI.Core.Prelude

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Environment.CertifiedSpatialTransportExact as Certified
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Papers.NavierStokes.TheoremInterfaceRound133Exact as NS

------------------------------------------------------------------------
-- LES FLUID-PHYSICS COUPLING
--
-- Repository-native cross-pollination owner.
--
-- BIDI discipline:
--   forward  : the repo already has an exact Navier-Stokes theorem lane and
--              certified spatial transport / chemistry transition grammars;
--   backward : hydrology, wind, solute transport and biological fluid uses
--              need an application-specific reduction from those physics into
--              the domain geometry, forcing, constitutive and boundary regime;
--   boundary : transport topology is not itself a fluid equation, and a
--              Navier-Stokes theorem does not automatically validate every
--              hydrological/atmospheric/biological reduction.
--
-- No external scientific claim is introduced here.  The module only makes the
-- repository reuse seam explicit.
------------------------------------------------------------------------

data FluidApplication : Set where
  surfaceWaterFlow
  groundwaterOrPorousFlow
  atmosphericWind
  dissolvedChemicalAdvection
  sedimentBearingFlow
  cellularOrTissueFluidTransport
  : FluidApplication

record FluidReductionReceipt : Set where
  constructor fluidReductionReceipt
  field
    application : FluidApplication
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

------------------------------------------------------------------------
-- Reaction/transport coupling.
--
-- Chemistry already owns transition grammar while SpatialTransport owns
-- directed support.  A coupled reaction-transport model additionally needs a
-- literal advection/diffusion weld.  Merely possessing both carriers proves no
-- PDE coupling.
------------------------------------------------------------------------

record ReactionTransportWeld
    {Source Target : Spatial.SpatialNode}
    (transportWitness : Certified.CertifiedSourceToObservation Source Target)
    : Set₁ where
  constructor reactionTransportWeld
  field
    chemicalTransition : Chemistry.Transition
    fluidCoupling : FluidTransportCoupling transportWitness
    concentrationCarrierReference : String
    advectionReference : String
    diffusionReference : String
    reactionSourceSinkReference : String
    conservationReference : String
    commonSpaceTimeCarrierReference : String

open ReactionTransportWeld public

------------------------------------------------------------------------
-- The existing NS paper interface is imported as the literal proof-lane owner,
-- rather than copying its PDE mathematics into LES.  Its Clay/frontier booleans
-- remain whatever that owner says; LES only records that a reusable physics
-- source exists.
------------------------------------------------------------------------

nsProofLaneReference : String
nsProofLaneReference =
  "DASHI.Papers.NavierStokes.TheoremInterfaceRound133Exact"

nsImportedClayPromotion : Bool
nsImportedClayPromotion = NS.round133PaperClayPromotion

nsImportedClayPromotionIsFalse : nsImportedClayPromotion ≡ false
nsImportedClayPromotionIsFalse = NS.round133PaperClayPromotionIsFalse

record LESFluidPhysicsBoundary : Set where
  constructor lesFluidPhysicsBoundary
  field
    transportPathIsNavierStokesSolution : Bool
    transportPathIsNavierStokesSolutionIsFalse :
      transportPathIsNavierStokesSolution ≡ false

    navierStokesLaneAutomaticallyValidatesHydrology : Bool
    navierStokesLaneAutomaticallyValidatesHydrologyIsFalse :
      navierStokesLaneAutomaticallyValidatesHydrology ≡ false

    groundwaterMustUseUnreducedIncompressibleNS : Bool
    groundwaterMustUseUnreducedIncompressibleNSIsFalse :
      groundwaterMustUseUnreducedIncompressibleNS ≡ false

    atmosphericWindIsIdenticalToClayNSProblem : Bool
    atmosphericWindIsIdenticalToClayNSProblemIsFalse :
      atmosphericWindIsIdenticalToClayNSProblem ≡ false

    chemistryTransitionPlusTransportPathProvesReactionTransportPDE : Bool
    chemistryTransitionPlusTransportPathProvesReactionTransportPDEIsFalse :
      chemistryTransitionPlusTransportPathProvesReactionTransportPDE ≡ false

    cellularFluidUseRequiresApplicationReduction : Bool
    cellularFluidUseRequiresApplicationReductionIsTrue :
      cellularFluidUseRequiresApplicationReduction ≡ true

canonicalLESFluidPhysicsBoundary : LESFluidPhysicsBoundary
canonicalLESFluidPhysicsBoundary =
  lesFluidPhysicsBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
