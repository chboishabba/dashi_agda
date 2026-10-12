module DASHI.Reasoning.TrialecticGrothendieckContextFibrationBridgeExact where

------------------------------------------------------------------------
-- TRIALECTIC GROTHENDIECK SITE -> CONTEXT-INDEXED OBSERVATION FIBRATION
--
-- The relational Stage-12 site and the generic context-indexed observation
-- calculus were developed independently.  Their category interfaces have the
-- same typed identity/composition content.  This file gives the exact adapter
-- and instantiates the existing T^18/T^9/T^3 cell presheaf as a
-- ContextIndexedObservation with identity observation.
--
-- Consequence: the generic canonical split-lift and factorisation-existence
-- machinery is now available on the actual relational Grothendieck site.
-- This does NOT establish Benabou cartesian uniqueness, Grothendieck
-- fibration/pseudofunctor equivalence, or a groupoid-valued presheaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude

import DASHI.Core.ContextIndexedObservationFibrationExact as Fibration
import DASHI.Core.ProjectionCategory as Cat
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf

open Cat.ProjectionCategory
open Fibration.ContextIndexedObservation

relationalProjectionCategory : Cat.ProjectionCategory
relationalProjectionCategory = record
  { Obj = Site.RelObj
  ; Hom = Site.RelHom
  ; id = λ {U} → Site.idR U
  ; _∘_ = Site.composeRel
  ; id-left = Site.composeRelIdLeft
  ; id-right = Site.composeRelIdRight
  ; assoc = Site.composeRelAssoc
  ; categoryReading =
      "Relational Stage-12 Grothendieck patch category viewed through ProjectionCategory"
  }

relationalCellIndexedObservation :
  Fibration.ContextIndexedObservation relationalProjectionCategory
relationalCellIndexedObservation = record
  { Fine = Presheaf.Section
  ; Surface = Presheaf.Section
  ; restrictFine = Presheaf.restrict
  ; restrictSurface = Presheaf.restrict
  ; observe = λ context section → section
  ; restrictFineIdentity = Presheaf.restrictIdentity
  ; restrictSurfaceIdentity = Presheaf.restrictIdentity
  ; restrictFineComposition =
      λ first second section →
        Presheaf.restrictComposition second first section
  ; restrictSurfaceComposition =
      λ first second section →
        Presheaf.restrictComposition second first section
  ; observationNaturality = λ change section → refl
  }

indexedFineAt :
  Site.RelObj → Set
indexedFineAt = Fibration.Fine relationalCellIndexedObservation

indexedFineAtGlobalIsT18 :
  indexedFineAt Site.globalABC ≡ Presheaf.Section Site.globalABC
indexedFineAtGlobalIsT18 = refl

indexedFineAtABIsT9 :
  indexedFineAt Site.edgeAB ≡ Presheaf.Section Site.edgeAB
indexedFineAtABIsT9 = refl

indexedFineAtAIsT3 :
  indexedFineAt Site.vertexA ≡ Presheaf.Section Site.vertexA
indexedFineAtAIsT3 = refl

relationalCanonicalSplitLift :
  {U V : Site.RelObj} →
  (change : Site.RelHom U V) →
  (target : Presheaf.Section V) →
  Fibration.TotalFineArrow
    relationalCellIndexedObservation
    (Fibration.cartesianSource
      relationalCellIndexedObservation
      change
      target)
    (V , target)
relationalCanonicalSplitLift change target =
  Fibration.canonicalSplitLift
    relationalCellIndexedObservation
    change
    target

relationalObservationCommutesWithRestriction :
  {U V : Site.RelObj} →
  (change : Site.RelHom U V) →
  (target : Presheaf.Section V) →
  Fibration.observe relationalCellIndexedObservation U
    (Fibration.restrictFine relationalCellIndexedObservation change target)
  ≡
  Fibration.restrictSurface relationalCellIndexedObservation change
    (Fibration.observe relationalCellIndexedObservation V target)
relationalObservationCommutesWithRestriction =
  Fibration.observationCommutesWithSplitLift
    relationalCellIndexedObservation

data ContextBridgeSuppliesFullBenabouUniqueness : Set where
data ContextBridgeSuppliesGrothendieckPseudofunctorEquivalence : Set where

contextBridgeDoesNotSupplyFullBenabouUniqueness :
  ContextBridgeSuppliesFullBenabouUniqueness → ⊥
contextBridgeDoesNotSupplyFullBenabouUniqueness ()

contextBridgeDoesNotSupplyFullGrothendieckEquivalence :
  ContextBridgeSuppliesGrothendieckPseudofunctorEquivalence → ⊥
contextBridgeDoesNotSupplyFullGrothendieckEquivalence ()

record TrialecticGrothendieckContextFibrationBridgeBoundary : Set where
  constructor trialectic-grothendieck-context-fibration-bridge-boundary
  field
    projectionCategoryAdapterPaid : Bool
    cellPresheafInstantiatesContextIndexedObservation : Bool
    restrictionNaturalityReused : Bool
    splitLiftExistenceReused : Bool
    fullBenabouUniquenessPromoted : Bool
    fullGrothendieckPseudofunctorEquivalencePromoted : Bool

open TrialecticGrothendieckContextFibrationBridgeBoundary public

canonicalTrialecticGrothendieckContextFibrationBridgeBoundary :
  TrialecticGrothendieckContextFibrationBridgeBoundary
canonicalTrialecticGrothendieckContextFibrationBridgeBoundary =
  trialectic-grothendieck-context-fibration-bridge-boundary
    true true true true false false
