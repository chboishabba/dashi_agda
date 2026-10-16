module DASHI.Philosophy.NonginExtendedRoadmapExact where

------------------------------------------------------------------------
-- NONGIN EXTENDED ROADMAP
--
-- Nongin core closure and attached research-lineage continuation are distinct.
-- The wave/369 cross-pollination advances the attached higher-descent lane to a
-- concrete full-site non-discrete groupoid presheaf, effective stack, setoid-
-- truncated higher stack, and finite one-truncated hypersheaf on the exact
-- triadic topology.  Arbitrary infinity-hypercover certification remains a
-- strictly stronger external frontier.
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

fullSiteGroupoidPresheafPaid :
  Attached.fullSiteGroupoidPresheafPaid attachedBoundary ≡ true
fullSiteGroupoidPresheafPaid = refl

effectiveStackPaid :
  Attached.effectiveStackPaid attachedBoundary ≡ true
effectiveStackPaid = refl

higherStackPaid :
  Attached.higherStackPaid attachedBoundary ≡ true
higherStackPaid = refl

finiteTriadicHypersheafPaid :
  Attached.finiteTriadicHypersheafPaid attachedBoundary ≡ true
finiteTriadicHypersheafPaid = refl

arbitraryInfinityHypersheafStillOpen :
  Attached.arbitraryInfinityHypersheafStillOpen attachedBoundary ≡ true
arbitraryInfinityHypersheafStillOpen = refl

physicalPromotionRemainsIndependent :
  Attached.attachmentClaimsPhysicalLawAlreadyPromoted attachedBoundary ≡ false
physicalPromotionRemainsIndependent = refl

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
    fullSiteNonDiscreteGroupoidPresheafPaid : Bool
    effectiveStackPaid : Bool
    higherStackPaid : Bool
    finiteTriadicHypersheafPaid : Bool
    arbitraryInfinityHypersheafStillOpen : Bool
    descendantCertificationBoundariesPreserved : Bool
    roadmapDetachesDescendantProgrammes : Bool

open NonginExtendedRoadmapBoundary public

canonicalNonginExtendedRoadmapBoundary : NonginExtendedRoadmapBoundary
canonicalNonginExtendedRoadmapBoundary =
  nongin-extended-roadmap-boundary
    true true true true true true true
    true true true true true true false
