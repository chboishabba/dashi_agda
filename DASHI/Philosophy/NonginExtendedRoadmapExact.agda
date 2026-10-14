module DASHI.Philosophy.NonginExtendedRoadmapExact where

------------------------------------------------------------------------
-- NONGIN EXTENDED ROADMAP
--
-- Nongin core closure and Nongin research-lineage continuation are distinct.
-- The semantic/genealogical reconstruction may be closed while the existing
-- descendant programmes remain attached to the same research lineage.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginRoadmapClosureExact as Core
import DASHI.Philosophy.NonginAttachedDescendantProgrammesExact as Attached

coreBoundary : Core.NonginRoadmapClosureBoundary
coreBoundary = Core.canonicalNonginRoadmapClosureBoundary

attachedBoundary : Attached.NonginAttachedDescendantProgrammesBoundary
attachedBoundary = Attached.canonicalNonginAttachedDescendantProgrammesBoundary

nonginCoreClosurePaid : Core.nonginRoadmapClosed coreBoundary ≡ true
nonginCoreClosurePaid = refl

attachedTransportStackProgrammePresent :
  Attached.transportStackLikeOwnerAttached attachedBoundary ≡ true
attachedTransportStackProgrammePresent = refl

attachedHyperfabricProgrammePresent :
  Attached.hyperfabricOwnerAttached attachedBoundary ≡ true
attachedHyperfabricProgrammePresent = refl

attachedHigherDescentProgrammePresent :
  Attached.higherDescentOwnerAttached attachedBoundary ≡ true
attachedHigherDescentProgrammePresent = refl

attachedExceptionalProgrammePresent :
  Attached.exceptionalProgrammeAttached attachedBoundary ≡ true
attachedExceptionalProgrammePresent = refl

attachedPhysicalPromotionProgrammePresent :
  Attached.physicalPromotionProgrammeAttached attachedBoundary ≡ true
attachedPhysicalPromotionProgrammePresent = refl

allDescendantProgrammesRemainAttached :
  Attached.descendantProgrammesRemainAttachedToNongin attachedBoundary ≡ true
allDescendantProgrammesRemainAttached = refl

-- Attachment is a roadmap/genealogy relation.  It does not silently flip the
-- stricter promotion guards inside the descendant owners.
attachmentDoesNotFakeHigherStackCertification :
  Attached.attachmentClaimsHigherStackAlreadyCertified attachedBoundary ≡ false
attachmentDoesNotFakeHigherStackCertification = refl

attachmentDoesNotFakePhysicalPromotion :
  Attached.attachmentClaimsPhysicalLawAlreadyPromoted attachedBoundary ≡ false
attachmentDoesNotFakePhysicalPromotion = refl

record NonginExtendedRoadmapBoundary : Set where
  constructor nongin-extended-roadmap-boundary
  field
    coreNonginRoadmapClosed : Bool
    transportStackProgrammeAttached : Bool
    hyperfabricProgrammeAttached : Bool
    higherDescentProgrammeAttached : Bool
    exceptionalProgrammeAttached : Bool
    physicalPromotionProgrammeAttached : Bool
    attachedLineageContinuesAfterCoreClosure : Bool
    descendantCertificationBoundariesPreserved : Bool
    roadmapDetachesDescendantProgrammes : Bool

open NonginExtendedRoadmapBoundary public

canonicalNonginExtendedRoadmapBoundary : NonginExtendedRoadmapBoundary
canonicalNonginExtendedRoadmapBoundary =
  nongin-extended-roadmap-boundary
    true true true true true true true true false
