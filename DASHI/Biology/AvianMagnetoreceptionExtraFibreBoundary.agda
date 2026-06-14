module DASHI.Biology.AvianMagnetoreceptionExtraFibreBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.AvianCompassSurface
open import DASHI.Biology.AvianHardProblemResidual
open import DASHI.Biology.ObserverPerceptualManifoldResidual

------------------------------------------------------------------------
-- Lemma 6: avian best-case extra-fibre boundary.
------------------------------------------------------------------------

record AvianMagnetoreceptionExtraFibreBoundary : Set₁ where
  field
    avianCompassBridgeReceipt :
      AvianCompassBridgeReceipt

    avianHardProblemResidualCertificate :
      AvianHardProblemResidualCertificate avianCompassBridgeReceipt

    avianHardProblemResidualCertificateIsCanonical :
      avianHardProblemResidualCertificate ≡
        avianBridgeHardProblemResidual avianCompassBridgeReceipt

    magnetoreceptionFibre :
      PerceptualFibre

    magnetoreceptionFibreIsBird :
      magnetoreceptionFibre ≡ birdMagnetoreceptionFibre

    perceptualQuotientGeometryExperimentallyConstrained :
      Bool

    perceptualQuotientGeometryExperimentallyConstrainedIsTrue :
      perceptualQuotientGeometryExperimentallyConstrained ≡ true

    qualiaGeometryClaim :
      Bool

    qualiaGeometryClaimIsFalse :
      qualiaGeometryClaim ≡ false

    extraFibrePhenomenalContentRecovered :
      Bool

    extraFibrePhenomenalContentRecoveredIsFalse :
      extraFibrePhenomenalContentRecovered ≡ false

    quotientGeometryClaimIsReplacementPositiveClaim :
      Bool

    quotientGeometryClaimIsReplacementPositiveClaimIsTrue :
      quotientGeometryClaimIsReplacementPositiveClaim ≡ true

    extraFibreNonPromotionReading :
      String

open AvianMagnetoreceptionExtraFibreBoundary public

canonicalAvianMagnetoreceptionExtraFibreBoundary :
  (receipt : AvianCompassBridgeReceipt) →
  AvianMagnetoreceptionExtraFibreBoundary
canonicalAvianMagnetoreceptionExtraFibreBoundary receipt =
  record
    { avianCompassBridgeReceipt =
        receipt
    ; avianHardProblemResidualCertificate =
        avianBridgeHardProblemResidual receipt
    ; avianHardProblemResidualCertificateIsCanonical =
        refl
    ; magnetoreceptionFibre =
        birdMagnetoreceptionFibre
    ; magnetoreceptionFibreIsBird =
        refl
    ; perceptualQuotientGeometryExperimentallyConstrained =
        true
    ; perceptualQuotientGeometryExperimentallyConstrainedIsTrue =
        refl
    ; qualiaGeometryClaim =
        false
    ; qualiaGeometryClaimIsFalse =
        refl
    ; extraFibrePhenomenalContentRecovered =
        false
    ; extraFibrePhenomenalContentRecoveredIsFalse =
        refl
    ; quotientGeometryClaimIsReplacementPositiveClaim =
        true
    ; quotientGeometryClaimIsReplacementPositiveClaimIsTrue =
        refl
    ; extraFibreNonPromotionReading =
        "Lemma 6 records the avian best case: the bridge receipt and hard-problem residual constrain bird magnetoreception as an experimentally bounded perceptual quotient geometry, while phenomenal content is not recovered and no qualia-geometry claim is promoted."
    }
