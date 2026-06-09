module DASHI.Unified.Everything where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Unified.ArithmeticMoonshine as ArithmeticMoonshine
import DASHI.Unified.BrainFMRI as BrainFMRI
import DASHI.Unified.CarrierGrammar as CarrierGrammar
import DASHI.Unified.ChemistrySupervoxel as ChemistrySupervoxel
import DASHI.Unified.CrossScaleMatterPhysics as CrossScaleMatterPhysics
import DASHI.Unified.FormalObjectParents as FormalObjectParents
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.PNFHyperfabric as PNFHyperfabric
import DASHI.Unified.Physics as Physics

canonicalUnifiedObjects : List Spine.UnifiedObjectInvariant
canonicalUnifiedObjects =
  CarrierGrammar.carrierGrammarObject
  ∷ ChemistrySupervoxel.chemistryObject
  ∷ ChemistrySupervoxel.supervoxelChemistryObject
  ∷ PNFHyperfabric.pnfHyperfabricObject
  ∷ BrainFMRI.brainFMRIObject
  ∷ ArithmeticMoonshine.arithmeticMoonshineObject
  ∷ Physics.navierStokesObject
  ∷ Physics.yangMillsObject
  ∷ CrossScaleMatterPhysics.crossScaleMatterPhysicsObject
  ∷ []

record UnifiedObjectTable : Setω where
  field
    objects :
      List Spine.UnifiedObjectInvariant

    objectsAreCanonical :
      objects ≡ canonicalUnifiedObjects

    allJProjectionExternalPromotion :
      Spine.UnifiedObjectInvariant → Bool

    allJProjectionExternalPromotionIsFalse :
      ∀ object → allJProjectionExternalPromotion object ≡ false

    allFormalProjectionExternalPromotion :
      Spine.UnifiedObjectInvariant → Spine.UniversalProjectionKind → Bool

    allFormalProjectionExternalPromotionIsFalse :
      ∀ object kind → allFormalProjectionExternalPromotion object kind ≡ false

    formalObjectParentSurface :
      FormalObjectParents.FormalObjectParentSurface

    crossScaleMatterPhysicsSurface :
      CrossScaleMatterPhysics.CrossScaleMatterPhysicsSurface

    plainPolicy :
      String

canonicalUnifiedObjectTable : UnifiedObjectTable
canonicalUnifiedObjectTable =
  record
    { objects =
        canonicalUnifiedObjects
    ; objectsAreCanonical =
        refl
    ; allJProjectionExternalPromotion =
        Spine.objectExternalJPromotion
    ; allJProjectionExternalPromotionIsFalse =
        Spine.objectExternalJPromotionIsFalse
    ; allFormalProjectionExternalPromotion =
        Spine.objectProjectionPromotion
    ; allFormalProjectionExternalPromotionIsFalse =
        Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    ; formalObjectParentSurface =
        FormalObjectParents.canonicalFormalObjectParentSurface
    ; crossScaleMatterPhysicsSurface =
        CrossScaleMatterPhysics.canonicalCrossScaleMatterPhysicsSurface
    ; plainPolicy =
        "Every unified facade object exposes observation, projection, carrier/role vector, residual, proof posture, invariant strength, and the required formal parent projection bundle. The bundle includes modular-j, Hecke, Bott, Kolmogorov, category, quotient, lattice, and operator projections. Literal authority is lane-specific; every formal projection has externalPromotion = false. The cross-scale matter/physics parent records the atoms-to-stellar composition ladder as structural and receipt-gated, with quantitative solar-style counterfactual prediction still blocked."
    }

brainFMRIRemainsNonPromoting :
  Spine.objectExternalJPromotion BrainFMRI.brainFMRIObject ≡ false
brainFMRIRemainsNonPromoting =
  refl

navierStokesRemainsNonPromoting :
  Spine.objectExternalJPromotion Physics.navierStokesObject ≡ false
navierStokesRemainsNonPromoting =
  refl

yangMillsRemainsNonPromoting :
  Spine.objectExternalJPromotion Physics.yangMillsObject ≡ false
yangMillsRemainsNonPromoting =
  refl

brainFMRIFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion BrainFMRI.brainFMRIObject kind ≡ false
brainFMRIFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    BrainFMRI.brainFMRIObject

navierStokesFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion Physics.navierStokesObject kind ≡ false
navierStokesFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    Physics.navierStokesObject

yangMillsFormalProjectionsRemainNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion Physics.yangMillsObject kind ≡ false
yangMillsFormalProjectionsRemainNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    Physics.yangMillsObject
