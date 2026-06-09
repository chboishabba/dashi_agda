module DASHI.Physics.Closure.FullYukawaEigenbasisReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Y13ComplexEntryReceipt as Y13

------------------------------------------------------------------------
-- Full complex down-type Yukawa eigenbasis diagnostic.
--
-- This receipt consumes the p2-p5 y13 diagnostic and records the numerical
-- diagonalisation surface.  The numerical values are diagnostics generated
-- by scripts/check_full_yukawa_eigenbasis.py, not certified Agda linear
-- algebra.

data FullYukawaEigenbasisStatus : Set where
  fullComplexYukawaDiagnosticRecorded :
    FullYukawaEigenbasisStatus

data FullYukawaEigenbasisBlocker : Set where
  missingCertifiedComplexEigenbasis :
    FullYukawaEigenbasisBlocker

  missingPhysicalNormalisationAuthority :
    FullYukawaEigenbasisBlocker

  missingPDGCKMAuthorityBinding :
    FullYukawaEigenbasisBlocker

  heckePhaseMismatchPersists :
    FullYukawaEigenbasisBlocker

canonicalFullYukawaEigenbasisBlockers :
  List FullYukawaEigenbasisBlocker
canonicalFullYukawaEigenbasisBlockers =
  missingCertifiedComplexEigenbasis
  ∷ missingPhysicalNormalisationAuthority
  ∷ missingPDGCKMAuthorityBinding
  ∷ heckePhaseMismatchPersists
  ∷ []

data FullYukawaEigenbasisPromotion : Set where

fullYukawaEigenbasisPromotionImpossibleHere :
  FullYukawaEigenbasisPromotion →
  ⊥
fullYukawaEigenbasisPromotionImpossibleHere ()

record FullYukawaEigenbasisReceipt : Set where
  field
    status :
      FullYukawaEigenbasisStatus

    y13Receipt :
      Y13.Y13ComplexEntryReceipt

    y13ReceiptIsCanonical :
      y13Receipt ≡ Y13.canonicalY13ComplexEntryReceipt

    matrixConvention :
      String

    diagonalisationScript :
      String

    eigenvalueDiagnosticLabel :
      String

    yukawaSingularValueDiagnosticLabel :
      String

    absCKMMatrixDiagnosticLabel :
      String

    vusDiagnostic :
      Float

    vcbDiagnostic :
      Float

    vubDiagnostic :
      Float

    vtdDiagnostic :
      Float

    eigenvalueRatioComparisonLabel :
      String

    ckmComparisonLabel :
      String

    fullYukawaEigenbasisDiagnosticRecorded :
      Bool

    fullYukawaEigenbasisDiagnosticRecordedIsTrue :
      fullYukawaEigenbasisDiagnosticRecorded ≡ true

    certifiedDiagonalisationConstructed :
      Bool

    certifiedDiagonalisationConstructedIsFalse :
      certifiedDiagonalisationConstructed ≡ false

    physicalEigenbasis :
      Bool

    physicalEigenbasisIsFalse :
      physicalEigenbasis ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List FullYukawaEigenbasisBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFullYukawaEigenbasisBlockers

    promotionFlags :
      List FullYukawaEigenbasisPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open FullYukawaEigenbasisReceipt public

canonicalFullYukawaEigenbasisReceipt :
  FullYukawaEigenbasisReceipt
canonicalFullYukawaEigenbasisReceipt =
  record
    { status =
        fullComplexYukawaDiagnosticRecorded
    ; y13Receipt =
        Y13.canonicalY13ComplexEntryReceipt
    ; y13ReceiptIsCanonical =
        refl
    ; matrixConvention =
        "Y_d uses alpha1 suppression by total lane distance; y13 enters as alpha1^3*(24*pi/sqrt6)*exp(i*delta_29)"
    ; diagonalisationScript =
        "scripts/check_full_yukawa_eigenbasis.py"
    ; eigenvalueDiagnosticLabel =
        "eigenvalues(Y_d^dagger Y_d) ~= [5.93906484e-09, 1.68554767e-03, 1.17527349e-01]"
    ; yukawaSingularValueDiagnosticLabel =
        "singular values ~= [0.0000770653, 0.0410554, 0.342823]"
    ; absCKMMatrixDiagnosticLabel =
        "|V| ~= [[0.648665,0.089765,0.755762],[0.749691,0.095891,0.654804],[0.131142,0.991336,0.007398]]"
    ; vusDiagnostic =
        0.08976502640935104
    ; vcbDiagnostic =
        0.6548044702987887
    ; vubDiagnostic =
        0.7557621132954778
    ; vtdDiagnostic =
        0.13114168
    ; eigenvalueRatioComparisonLabel =
        "The diagnostic singular-value hierarchy is not yet an accepted down-quark mass-ratio match"
    ; ckmComparisonLabel =
        "The diagnostic CKM matrix is a poor physical match; it records the current fully specified convention"
    ; fullYukawaEigenbasisDiagnosticRecorded =
        true
    ; fullYukawaEigenbasisDiagnosticRecordedIsTrue =
        refl
    ; certifiedDiagonalisationConstructed =
        false
    ; certifiedDiagonalisationConstructedIsFalse =
        refl
    ; physicalEigenbasis =
        false
    ; physicalEigenbasisIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalFullYukawaEigenbasisBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The full complex matrix is now numerically specified as a diagnostic"
        ∷ "The numerical diagonalisation is not certified in Agda"
        ∷ "The resulting matrix does not promote a physical CKM claim"
        ∷ []
    }

fullYukawaEigenbasisDiagnosticIsRecorded :
  fullYukawaEigenbasisDiagnosticRecorded canonicalFullYukawaEigenbasisReceipt ≡ true
fullYukawaEigenbasisDiagnosticIsRecorded =
  refl

fullYukawaEigenbasisDoesNotPromoteCKM :
  physicalCKMPromoted canonicalFullYukawaEigenbasisReceipt ≡ false
fullYukawaEigenbasisDoesNotPromoteCKM =
  refl

