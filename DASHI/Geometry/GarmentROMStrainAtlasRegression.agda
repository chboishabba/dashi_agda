module DASHI.Geometry.GarmentROMStrainAtlasRegression where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.GarmentROMStrainAtlas

------------------------------------------------------------------------
-- Compact import/regression surface.
--
-- Any complete bridge carries the canonical non-promotion certificate and
-- therefore cannot silently identify a finite pose cover with the full human
-- ROM or promote uncalibrated geometry to comfort/injury authority.

finiteCoverClaimClosed :
  (bridge : GarmentROMStrainAtlasBridge) →
  finiteCoverEqualsFullROMClaim bridge ≡ false
finiteCoverClaimClosed bridge =
  finiteCoverEqualsFullROMClaimIsFalse bridge

uncalibratedAuthorityClosed :
  (bridge : GarmentROMStrainAtlasBridge) →
  uncalibratedPhysicalAuthorityClaim bridge ≡ false
uncalibratedAuthorityClosed bridge =
  uncalibratedPhysicalAuthorityClaimIsFalse bridge

comfortInjuryAuthorityClosed :
  (bridge : GarmentROMStrainAtlasBridge) →
  comfortOrInjuryAuthorityClaim bridge ≡ false
comfortInjuryAuthorityClosed bridge =
  comfortOrInjuryAuthorityClaimIsFalse bridge

canonicalCertificateAvailable :
  (bridge : GarmentROMStrainAtlasBridge) →
  GarmentROMNonPromotionCertificate bridge
canonicalCertificateAvailable =
  canonicalGarmentROMNonPromotionCertificate
