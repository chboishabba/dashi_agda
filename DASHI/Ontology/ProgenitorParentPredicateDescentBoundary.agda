module DASHI.Ontology.ProgenitorParentPredicateDescentBoundary where

open import DASHI.Core.Prelude
import DASHI.Core.PredicatePullbackLatticeExact as Predicate

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice

------------------------------------------------------------------------
-- Coarse Wikidata predicates descend by construction.
------------------------------------------------------------------------

isP8810 : Predicate.Predicate WikidataParentSlot
isP8810 fatherP22 = false
isP8810 motherP25 = false
isP8810 parentP8810 = true
isP8810 hybridOfP1531 = false

p8810SurfacePredicate : Predicate.Predicate ParentCarrier
p8810SurfacePredicate = Predicate.pullbackPredicate projectParentSlot isP8810

p8810SurfacePredicateIsFibreConstant :
  Predicate.FibreConstantPredicate projectParentSlot p8810SurfacePredicate
p8810SurfacePredicateIsFibreConstant =
  Predicate.pulledBackPredicateIsFibreConstant projectParentSlot isP8810

------------------------------------------------------------------------
-- Fine semantic coordinates need not descend through the slot quotient.
------------------------------------------------------------------------

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

geneticPredicateNotFibreConstant :
  Predicate.FibreConstantPredicate projectParentSlot geneticP → ⊥
geneticPredicateNotFibreConstant constant =
  trueNotFalse
    (constant anonymousDonorCarrier adoptiveCarrier refl)

genealogicalParentPredicateNotFibreConstant :
  Predicate.FibreConstantPredicate projectParentSlot genealogicalParentP → ⊥
genealogicalParentPredicateNotFibreConstant constant =
  falseNotTrue
    (constant anonymousDonorCarrier adoptiveCarrier refl)

progenitorPredicateNotFibreConstantOnP8810 :
  Predicate.FibreConstantPredicate projectParentSlot progenitorP → ⊥
progenitorPredicateNotFibreConstantOnP8810 constant =
  trueNotFalse
    (constant anonymousDonorCarrier adoptiveCarrier refl)

------------------------------------------------------------------------
-- Therefore a slot-only public ontology cannot faithfully encode those
-- independently varying coordinates without a richer surface or residual.
------------------------------------------------------------------------

record ParentPredicateDescentBoundary : Set where
  constructor parentPredicateDescentBoundary
  field
    wikidataSlotPredicatesDescend : Bool
    wikidataSlotPredicatesDescendIsTrue : wikidataSlotPredicatesDescend ≡ true
    geneticCoordinateDescendsThroughSlot : Bool
    geneticCoordinateDescendsThroughSlotIsFalse :
      geneticCoordinateDescendsThroughSlot ≡ false
    genealogicalParentCoordinateDescendsThroughSlot : Bool
    genealogicalParentCoordinateDescendsThroughSlotIsFalse :
      genealogicalParentCoordinateDescendsThroughSlot ≡ false
    progenitorCoordinateDescendsThroughP8810Slot : Bool
    progenitorCoordinateDescendsThroughP8810SlotIsFalse :
      progenitorCoordinateDescendsThroughP8810Slot ≡ false

canonicalParentPredicateDescentBoundary : ParentPredicateDescentBoundary
canonicalParentPredicateDescentBoundary =
  parentPredicateDescentBoundary true refl false refl false refl false refl
