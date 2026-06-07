module DASHI.Unified.CrossScaleMatterPhysics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PhysicsChemistryBiologyDNAUnificationDischarge as PCB
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine

------------------------------------------------------------------------
-- Cross-scale matter/physics parent.
--
-- This is the parent spine for the grand composition story:
--
--   atoms -> molecules -> chemistry -> cells -> organisms -> stellar bodies
--
-- Forces and field carriers explain why atomic/molecular configurations are
-- stable or unstable, but current DASHI only records this as a typed
-- receipt-gated scaffold.  It does not yet promote quantitative prediction
-- such as "a 3% hydrogen perturbation makes the Sun unstable".

data MatterScale : Set where
  atomScale : MatterScale
  moleculeScale : MatterScale
  chemistryScale : MatterScale
  cellScale : MatterScale
  organismScale : MatterScale
  stellarScale : MatterScale

data FundamentalInteractionCarrier : Set where
  strongNuclearInteraction : FundamentalInteractionCarrier
  weakInteraction : FundamentalInteractionCarrier
  electromagneticInteraction : FundamentalInteractionCarrier
  gravitationalInteraction : FundamentalInteractionCarrier

data CrossScalePredictionStatus : Set where
  structuralCompositionLadderPresent : CrossScalePredictionStatus
  quantitativeCrossScalePredictionBlocked : CrossScalePredictionStatus
  stellarCompositionCounterfactualBlocked : CrossScalePredictionStatus

canonicalMatterScales : List MatterScale
canonicalMatterScales =
  atomScale
  ∷ moleculeScale
  ∷ chemistryScale
  ∷ cellScale
  ∷ organismScale
  ∷ stellarScale
  ∷ []

canonicalInteractionCarriers : List FundamentalInteractionCarrier
canonicalInteractionCarriers =
  strongNuclearInteraction
  ∷ weakInteraction
  ∷ electromagneticInteraction
  ∷ gravitationalInteraction
  ∷ []

scaleCarrier : MatterScale → Unified.LanguageCarrier
scaleCarrier atomScale =
  Unified.atomCarrier
scaleCarrier moleculeScale =
  Unified.moleculeCarrier
scaleCarrier chemistryScale =
  Unified.chemistryChannelCarrier
scaleCarrier cellScale =
  Unified.cellCarrier
scaleCarrier organismScale =
  Unified.organismCarrier
scaleCarrier stellarScale =
  Unified.stellarCarrier

interactionCarrier :
  FundamentalInteractionCarrier → Unified.LanguageCarrier
interactionCarrier strongNuclearInteraction =
  Unified.nuclearForceCarrier
interactionCarrier weakInteraction =
  Unified.weakForceCarrier
interactionCarrier electromagneticInteraction =
  Unified.electromagneticForceCarrier
interactionCarrier gravitationalInteraction =
  Unified.gravityForceCarrier

record CrossScaleMatterPhysicsSurface : Setω where
  field
    physicsChemistryBiologyDNADischarge :
      PCB.PhysicsChemistryBiologyDNAUnificationDischarge

    physicsChemistryBiologyDNADischargePromoted :
      Bool

    physicsChemistryBiologyDNADischargePromotedIsFalse :
      physicsChemistryBiologyDNADischargePromoted ≡ false

    matterScales :
      List MatterScale

    matterScalesAreCanonical :
      matterScales ≡ canonicalMatterScales

    interactions :
      List FundamentalInteractionCarrier

    interactionsAreCanonical :
      interactions ≡ canonicalInteractionCarriers

    carrierOfScale :
      MatterScale → Unified.LanguageCarrier

    carrierOfScaleIsCanonical :
      carrierOfScale ≡ scaleCarrier

    carrierOfInteraction :
      FundamentalInteractionCarrier → Unified.LanguageCarrier

    carrierOfInteractionIsCanonical :
      carrierOfInteraction ≡ interactionCarrier

    status :
      CrossScalePredictionStatus

    quantitativePredictionPromoted :
      Bool

    quantitativePredictionPromotedIsFalse :
      quantitativePredictionPromoted ≡ false

    sunHydrogenCounterfactualPromoted :
      Bool

    sunHydrogenCounterfactualPromotedIsFalse :
      sunHydrogenCounterfactualPromoted ≡ false

    plainReading :
      String

canonicalCrossScaleMatterPhysicsSurface :
  CrossScaleMatterPhysicsSurface
canonicalCrossScaleMatterPhysicsSurface =
  record
    { physicsChemistryBiologyDNADischarge =
        PCB.canonicalPhysicsChemistryBiologyDNAUnificationDischarge
    ; physicsChemistryBiologyDNADischargePromoted =
        false
    ; physicsChemistryBiologyDNADischargePromotedIsFalse =
        refl
    ; matterScales =
        canonicalMatterScales
    ; matterScalesAreCanonical =
        refl
    ; interactions =
        canonicalInteractionCarriers
    ; interactionsAreCanonical =
        refl
    ; carrierOfScale =
        scaleCarrier
    ; carrierOfScaleIsCanonical =
        refl
    ; carrierOfInteraction =
        interactionCarrier
    ; carrierOfInteractionIsCanonical =
        refl
    ; status =
        structuralCompositionLadderPresent
    ; quantitativePredictionPromoted =
        false
    ; quantitativePredictionPromotedIsFalse =
        refl
    ; sunHydrogenCounterfactualPromoted =
        false
    ; sunHydrogenCounterfactualPromotedIsFalse =
        refl
    ; plainReading =
        "DASHI has a structural cross-scale matter ladder from atoms to molecules, chemistry, cells, organisms, and stellar bodies, with strong, weak, electromagnetic, and gravitational carriers explaining configuration stability. The existing physics/chemistry/biology/DNA discharge plugs these lanes together as receipt-gated observation transport only. Quantitative cross-scale prediction, including solar composition counterfactuals such as a hydrogen perturbation stability claim, remains blocked until the required physical models, constants, equations of state, transport solvers, and empirical validation receipts are inhabited."
    }

crossScaleMatterPhysicsObject : Spine.UnifiedObjectInvariant
crossScaleMatterPhysicsObject =
  Spine.unifiedObjectInvariant
    "cross-scale-matter-physics-parent"
    Unified.physicsLane
    "atoms, molecules, cells, organisms, and stellar composition observations"
    "composition ladder -> force carriers -> stability/counterfactual boundary"
    Unified.stellarCarrier
    (Spine.defaultRoleVector "cross-scale-matter-physics-parent")
    Residual.partial
    Asserted.internalConditionalProof
    Spine.softInvariant
    (Spine.blockedJProjection "cross-scale matter physics has no literal modular-j bridge")
    (Spine.blockedFormalProjectionBundle "cross-scale matter physics projections are present but quantitative prediction bridges are blocked")

crossScaleQuantitativePredictionBlocked :
  CrossScaleMatterPhysicsSurface.quantitativePredictionPromoted
    canonicalCrossScaleMatterPhysicsSurface
  ≡
  false
crossScaleQuantitativePredictionBlocked =
  refl

sunHydrogenCounterfactualBlocked :
  CrossScaleMatterPhysicsSurface.sunHydrogenCounterfactualPromoted
    canonicalCrossScaleMatterPhysicsSurface
  ≡
  false
sunHydrogenCounterfactualBlocked =
  refl
