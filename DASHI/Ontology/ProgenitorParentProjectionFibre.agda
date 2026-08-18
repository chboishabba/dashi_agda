module DASHI.Ontology.ProgenitorParentProjectionFibre where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.ProgenitorParentHyperfabric

------------------------------------------------------------------------
-- Exact fibre over the Wikidata parent-slot projection.
------------------------------------------------------------------------

record ParentCarrier : Set where
  constructor parentCarrier
  field
    carrierLevel : NodeLevel
    carrierRelation : RelationVector
open ParentCarrier public

projectParentSlot : ParentCarrier → WikidataParentSlot
projectParentSlot carrier = recommendedGenericSlot (carrierLevel carrier)

record ParentSlotFibre (slot : WikidataParentSlot) : Set where
  constructor parentSlotFibre
  field
    fibreCarrier : ParentCarrier
    fibreExact : projectParentSlot fibreCarrier ≡ slot
open ParentSlotFibre public

anonymousDonorCarrier : ParentCarrier
anonymousDonorCarrier = parentCarrier individualLevel anonymousIVFDonor

adoptiveCarrier : ParentCarrier
adoptiveCarrier = parentCarrier individualLevel adoptiveParent

cultivarCarrier : ParentCarrier
cultivarCarrier = parentCarrier lineageLevel (relation cultivarLineageProjection)

anonymousDonorInP8810Fibre : ParentSlotFibre parentP8810
anonymousDonorInP8810Fibre = parentSlotFibre anonymousDonorCarrier refl

adoptiveParentInP8810Fibre : ParentSlotFibre parentP8810
adoptiveParentInP8810Fibre = parentSlotFibre adoptiveCarrier refl

cultivarInP1531Fibre : ParentSlotFibre hybridOfP1531
cultivarInP1531Fibre = parentSlotFibre cultivarCarrier refl

p8810FibreContainsGeneticallyDistinctCarriers :
  geneticContributor (carrierRelation anonymousDonorCarrier) ≡ true
  × geneticContributor (carrierRelation adoptiveCarrier) ≡ false
p8810FibreContainsGeneticallyDistinctCarriers = refl , refl

-- P1531 specializes the visible representation while preserving progeniture;
-- it does not force the lineage relation into genealogical/social parenthood.
p1531SpecializationPreservesProgenitorCoordinate :
  projectParentSlot cultivarCarrier ≡ hybridOfP1531
  × progenitorRelation (carrierRelation cultivarCarrier) ≡ true
  × genealogicalParent (carrierRelation cultivarCarrier) ≡ false
p1531SpecializationPreservesProgenitorCoordinate = refl , (refl , refl)

record CompatibleParentView : Set where
  constructor compatibleParentView
  field
    hiddenCarrier : ParentCarrier
    visibleSlot : WikidataParentSlot
    compatible : projectParentSlot hiddenCarrier ≡ visibleSlot
open CompatibleParentView public

forgetCompatibility : CompatibleParentView → ParentCarrier
forgetCompatibility view = hiddenCarrier view

liftCarrier : ParentCarrier → CompatibleParentView
liftCarrier carrier = compatibleParentView carrier (projectParentSlot carrier) refl

forgetAfterLift :
  (carrier : ParentCarrier) →
  forgetCompatibility (liftCarrier carrier) ≡ carrier
forgetAfterLift carrier = refl

carrierRetractionIsExact :
  (carrier : ParentCarrier) →
  carrierRelation (forgetCompatibility (liftCarrier carrier))
  ≡ carrierRelation carrier
carrierRetractionIsExact carrier = refl
