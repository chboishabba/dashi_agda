module DASHI.Physics.Closure.CKMFromYukawaEigenbasisReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YukawaMatrixFullReceipt as YFull

------------------------------------------------------------------------
-- CKM-from-Yukawa-eigenbasis diagnostic.
--
-- The current receipt records the diagonalisation task and the available
-- numerical targets.  The missing p2-p5 y13 entry and absence of a certified
-- diagonaliser keep the physical CKM promotion false.

data CKMFromYukawaEigenbasisStatus : Set where
  numericalDiagonalisationSurfaceRecorded :
    CKMFromYukawaEigenbasisStatus

data CKMFromYukawaEigenbasisBlocker : Set where
  missingP2P5YukawaEntry :
    CKMFromYukawaEigenbasisBlocker

  missingCertifiedEigenbasisComputation :
    CKMFromYukawaEigenbasisBlocker

  missingPDGCKMAuthorityBinding :
    CKMFromYukawaEigenbasisBlocker

canonicalCKMFromYukawaEigenbasisBlockers :
  List CKMFromYukawaEigenbasisBlocker
canonicalCKMFromYukawaEigenbasisBlockers =
  missingP2P5YukawaEntry
  ∷ missingCertifiedEigenbasisComputation
  ∷ missingPDGCKMAuthorityBinding
  ∷ []

data CKMFromYukawaPromotion : Set where

ckmFromYukawaPromotionImpossibleHere :
  CKMFromYukawaPromotion →
  ⊥
ckmFromYukawaPromotionImpossibleHere ()

record CKMFromYukawaEigenbasisReceipt : Set where
  field
    status :
      CKMFromYukawaEigenbasisStatus

    yukawaMatrixReceipt :
      YFull.YukawaMatrixFullReceipt

    yukawaMatrixReceiptIsCanonical :
      yukawaMatrixReceipt ≡ YFull.canonicalYukawaMatrixFullReceipt

    diagonalisationFormula :
      String

    upSectorBasisAssumption :
      String

    vMatrixFormula :
      String

    vusDiagnostic :
      Float

    vusDiagnosticLabel :
      String

    vcbDiagnostic :
      Float

    vcbDiagnosticLabel :
      String

    vubDiagnosticLabel :
      String

    vtdDiagnosticLabel :
      String

    ckmNumericalDiagonalisationRecorded :
      Bool

    ckmNumericalDiagonalisationRecordedIsTrue :
      ckmNumericalDiagonalisationRecorded ≡ true

    certifiedNumericalDiagonalisationConstructed :
      Bool

    certifiedNumericalDiagonalisationConstructedIsFalse :
      certifiedNumericalDiagonalisationConstructed ≡ false

    cabibboAngleDerived :
      Bool

    cabibboAngleDerivedIsFalse :
      cabibboAngleDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMFromYukawaEigenbasisBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMFromYukawaEigenbasisBlockers

    promotionFlags :
      List CKMFromYukawaPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMFromYukawaEigenbasisReceipt public

canonicalCKMFromYukawaEigenbasisReceipt :
  CKMFromYukawaEigenbasisReceipt
canonicalCKMFromYukawaEigenbasisReceipt =
  record
    { status =
        numericalDiagonalisationSurfaceRecorded
    ; yukawaMatrixReceipt =
        YFull.canonicalYukawaMatrixFullReceipt
    ; yukawaMatrixReceiptIsCanonical =
        refl
    ; diagonalisationFormula =
        "U_d diagonalises Y_d^dagger Y_d; V = U_u^dagger U_d"
    ; upSectorBasisAssumption =
        "current carrier diagnostic assumes U_u = identity"
    ; vMatrixFormula =
        "V = U_d under the current up-sector basis assumption"
    ; vusDiagnostic =
        0.08706965866119645
    ; vusDiagnosticLabel =
        "|V_us| from numerical diagonalisation of YukawaMatrixFullReceipt with y13=0 diagnostic convention"
    ; vcbDiagnostic =
        0.6548166787155723
    ; vcbDiagnosticLabel =
        "|V_cb| from numerical diagonalisation with y13=0; mismatch shows this convention is not physical"
    ; vubDiagnosticLabel =
        "|V_ub| diagnostic with y13=0 is approximately 0.755786; p2-p5 entry is open"
    ; vtdDiagnosticLabel =
        "|V_td| diagnostic with y13=0 is approximately 0.131092; p2-p5 entry is open"
    ; ckmNumericalDiagonalisationRecorded =
        true
    ; ckmNumericalDiagonalisationRecordedIsTrue =
        refl
    ; certifiedNumericalDiagonalisationConstructed =
        false
    ; certifiedNumericalDiagonalisationConstructedIsFalse =
        refl
    ; cabibboAngleDerived =
        false
    ; cabibboAngleDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMFromYukawaEigenbasisBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The receipt records the CKM diagonalisation surface and current y13=0 numerical diagnostics"
        ∷ "The resulting matrix is not a physical CKM match"
        ∷ "It does not certify a physical eigenbasis because the p2-p5 Yukawa entry is open"
        ∷ "Cabibbo-angle and physical CKM promotions remain false"
        ∷ []
    }

ckmFromYukawaDoesNotPromoteCabibbo :
  cabibboAngleDerived canonicalCKMFromYukawaEigenbasisReceipt ≡ false
ckmFromYukawaDoesNotPromoteCabibbo =
  refl
