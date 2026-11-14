module DASHI.Philosophy.NonginExtendedRoadmapValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginExtendedRoadmapExact as Roadmap

boundary : Roadmap.NonginExtendedRoadmapBoundary
boundary = Roadmap.canonicalNonginExtendedRoadmapBoundary

coreClosed : Roadmap.coreNonginRoadmapClosed boundary ≡ true
coreClosed = refl

transportAttached : Roadmap.transportStackProgrammeAttached boundary ≡ true
transportAttached = refl

hyperfabricAttached : Roadmap.hyperfabricProgrammeAttached boundary ≡ true
hyperfabricAttached = refl

higherDescentAttached : Roadmap.higherDescentProgrammeAttached boundary ≡ true
higherDescentAttached = refl

exceptionalAttached : Roadmap.exceptionalProgrammeAttached boundary ≡ true
exceptionalAttached = refl

physicalAttached : Roadmap.physicalPromotionProgrammeAttached boundary ≡ true
physicalAttached = refl

lineageContinues : Roadmap.attachedLineageContinuesAfterCoreClosure boundary ≡ true
lineageContinues = refl

fullSiteGroupoidPresheafPaid :
  Roadmap.fullSiteNonDiscreteGroupoidPresheafPaid boundary ≡ true
fullSiteGroupoidPresheafPaid = refl

effectiveStackPaid : Roadmap.effectiveStackPaid boundary ≡ true
effectiveStackPaid = refl

higherStackPaid : Roadmap.higherStackPaid boundary ≡ true
higherStackPaid = refl

finiteTriadicHypersheafPaid :
  Roadmap.finiteTriadicHypersheafPaid boundary ≡ true
finiteTriadicHypersheafPaid = refl

arbitraryInfinityHypersheafStillOpen :
  Roadmap.arbitraryInfinityHypersheafStillOpen boundary ≡ true
arbitraryInfinityHypersheafStillOpen = refl

certificationBoundariesPreserved :
  Roadmap.descendantCertificationBoundariesPreserved boundary ≡ true
certificationBoundariesPreserved = refl

roadmapDoesNotDetachDescendants :
  Roadmap.roadmapDetachesDescendantProgrammes boundary ≡ false
roadmapDoesNotDetachDescendants = refl
