module DASHI.Environment.LESPhysicsDomainCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESBioelectricGaugeChemistryExact as Bioelectric

------------------------------------------------------------------------
-- LES PHYSICS -> DOMAIN BIDI ASSEMBLY
--
-- Recent NS/YM proof PRs repeatedly gain leverage by preferring same-object /
-- source-identification adapters over duplicate estimates.  This LES owner
-- applies the same discipline at the application boundary:
--
--   existing physical theorem/geometry owner
--            + literal application reduction / identification receipt
--            + domain validation receipt
--            -> application mechanism socket
--
-- No theorem here claims that a physical proof lane automatically supplies a
-- hydrology, atmosphere, chemistry, cell or neural model.
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
    constitutiveReference : String
    boundaryGeometryReference : String
    scaleRegimeReference : String
    validationReference : String

open PhysicsToDomainWeld public

------------------------------------------------------------------------
-- Backward target from Stage 7.
--
-- The physical-domain weld is useful only when it can populate a real domain
-- state/evolution/observation surface.  We therefore keep the existing generic
-- DomainMechanismSocket as the exact downstream target rather than inventing a
-- second inference architecture here.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Current shortest architecture cut.
------------------------------------------------------------------------

record LESPhysicsCrossPollinationCutset : Set where
  constructor lesPhysicsCrossPollinationCutset
  field
    navierStokesLaneReferenced : Bool
    certifiedSpatialTransportReferenced : Bool
    reactionTransportWeldTyped : Bool
    bioelectricChemistryLaneReferenced : Bool
    suNGaugeLaneReferencedWithBoundary : Bool
    electrochemicalFieldSocketTyped : Bool

    applicationFluidReductionStillNeedsDomainReceipt : Bool
    quantitativeElectromagneticU1OwnerStillNeeded : Bool
    dimensionedElectricalQuantityOwnerStillNeeded : Bool
    electrodiffusionMembraneMechanismStillNeeded : Bool
    plantFluidPhysiologyWeldStillNeeded : Bool
    atmosphereHydrologyConstitutiveWeldsStillNeeded : Bool
    stage7ValidationStillNeeded : Bool

open LESPhysicsCrossPollinationCutset public

canonicalLESPhysicsCrossPollinationCutset : LESPhysicsCrossPollinationCutset
canonicalLESPhysicsCrossPollinationCutset =
  lesPhysicsCrossPollinationCutset
    true true true true true true
    true true true true true true true

record LESPhysicsCrossPollinationBoundary : Set where
  constructor lesPhysicsCrossPollinationBoundary
  field
    physicalTheoremOwnerIsApplicationModel : Bool
    physicalTheoremOwnerIsApplicationModelIsFalse :
      physicalTheoremOwnerIsApplicationModel ≡ false

    sharedMathematicalStructureIsSharedEmpiricalMechanism : Bool
    sharedMathematicalStructureIsSharedEmpiricalMechanismIsFalse :
      sharedMathematicalStructureIsSharedEmpiricalMechanism ≡ false

    sameObjectIdentificationMayReplaceDuplicateApplicationProof : Bool
    sameObjectIdentificationMayReplaceDuplicateApplicationProofIsTrue :
      sameObjectIdentificationMayReplaceDuplicateApplicationProof ≡ true

    reductionReceiptStillNeedsRegimeValidation : Bool
    reductionReceiptStillNeedsRegimeValidationIsTrue :
      reductionReceiptStillNeedsRegimeValidation ≡ true

canonicalLESPhysicsCrossPollinationBoundary : LESPhysicsCrossPollinationBoundary
canonicalLESPhysicsCrossPollinationBoundary =
  lesPhysicsCrossPollinationBoundary
    false refl
    false refl
    true refl
    true refl
