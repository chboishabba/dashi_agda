module DASHI.Ontology.ProgenitorParentProjectionFibre where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.ProgenitorParentHyperfabric

------------------------------------------------------------------------
-- Exact fibre over the Wikidata parent-slot projection.
--
-- This specializes the existing DASHI projection-fibre idea to parenting:
-- multiple carrier semantics can inhabit the same P22/P25/P8810/P1531 surface.
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

-- Same observable slot, incompatible genetic coordinates: observational
-- agreement at P8810 cannot recover the parent carrier.
p8810FibreContainsGeneticallyDistinctCarriers :
  geneticContributor (carrierRelation anonymousDonorCarrier) ≡ true
  × geneticContributor (carrierRelation adoptiveCarrier) ≡ false
p8810FibreContainsGeneticallyDistinctCarriers = refl , refl

-- The lineage projection changes the preferred Wikidata surface while retaining
-- the lineage/genealogical coordinate. This is representation specialization,
-- not a proof that cultivars are ontologically ineligible for progeniture.
p1531SpecializationPreservesLineageParentCoordinate :
  projectParentSlot cultivarCarrier ≡ hybridOfP1531
  × genealogicalParent (carrierRelation cultivarCarrier) ≡ true
p1531SpecializationPreservesLineageParentCoordinate = refl , refl

-- Projection compatibility object: a surface and hidden carrier are paired only
-- when the surface is exactly the carrier's projection. This is the concrete
-- parenting analogue of the pullback/fibre-product discipline used in the Lean
-- ontology work: compatibility is retained without identifying the views.
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

-- The carrier is therefore a retract of the compatible surface-plus-carrier
-- representation. The retraction preserves hidden semantics rather than
-- pretending that the visible slot determines them.
carrierRetractionIsExact :
  (carrier : ParentCarrier) →
  carrierRelation (forgetCompatibility (liftCarrier carrier))
  ≡ carrierRelation carrier
carrierRetractionIsExact carrier = refl
