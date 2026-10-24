module DASHI.Philosophy.NonginAttachedDescendantProgrammesValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginAttachedDescendantProgrammesExact as Attached

boundary : Attached.NonginAttachedDescendantProgrammesBoundary
boundary = Attached.canonicalNonginAttachedDescendantProgrammesBoundary

transportStackLikeOwnerAttached : Attached.transportStackLikeOwnerAttached boundary ≡ true
transportStackLikeOwnerAttached = refl

hyperfabricOwnerAttached : Attached.hyperfabricOwnerAttached boundary ≡ true
hyperfabricOwnerAttached = refl

higherDescentOwnerAttached : Attached.higherDescentOwnerAttached boundary ≡ true
higherDescentOwnerAttached = refl

exceptionalProgrammeAttached : Attached.exceptionalProgrammeAttached boundary ≡ true
exceptionalProgrammeAttached = refl

physicalPromotionProgrammeAttached : Attached.physicalPromotionProgrammeAttached boundary ≡ true
physicalPromotionProgrammeAttached = refl

descendantsRemainAttached : Attached.descendantProgrammesRemainAttachedToNongin boundary ≡ true
descendantsRemainAttached = refl

fullSiteGroupoidPresheafPaid : Attached.fullSiteGroupoidPresheafPaid boundary ≡ true
fullSiteGroupoidPresheafPaid = refl

effectiveStackPaid : Attached.effectiveStackPaid boundary ≡ true
effectiveStackPaid = refl

higherStackPaid : Attached.higherStackPaid boundary ≡ true
higherStackPaid = refl

finiteTriadicHypersheafPaid : Attached.finiteTriadicHypersheafPaid boundary ≡ true
finiteTriadicHypersheafPaid = refl

arbitraryInfinityHypersheafStillOpen :
  Attached.arbitraryInfinityHypersheafStillOpen boundary ≡ true
arbitraryInfinityHypersheafStillOpen = refl

physicalPromotionRemainsSeparate : Attached.attachmentClaimsPhysicalLawAlreadyPromoted boundary ≡ false
physicalPromotionRemainsSeparate = refl

independentOwnersPreserved : Attached.attachmentCollapsesIndependentTheoremOwnership boundary ≡ false
independentOwnersPreserved = refl
