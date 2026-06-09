module DASHI.Physics.Closure.PhysicalMassMatrixReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.OSPositivityDissolvedReceipt as OS
import DASHI.Physics.Closure.Y13ComplexEntryReceipt as Y13

------------------------------------------------------------------------
-- VEV-calibrated physical mass matrix diagnostic.

data PhysicalMassMatrixStatus : Set where
  pdgVEVCalibratedMassMatrixDiagnosticRecorded :
    PhysicalMassMatrixStatus

data PhysicalMassMatrixBlocker : Set where
  vevIsExternalPDGInput :
    PhysicalMassMatrixBlocker

  missingCarrierDerivedVEV :
    PhysicalMassMatrixBlocker

  massSpectrumDoesNotMatchPDG :
    PhysicalMassMatrixBlocker

  missingCertifiedDiagonalisation :
    PhysicalMassMatrixBlocker

canonicalPhysicalMassMatrixBlockers :
  List PhysicalMassMatrixBlocker
canonicalPhysicalMassMatrixBlockers =
  vevIsExternalPDGInput
  ∷ missingCarrierDerivedVEV
  ∷ massSpectrumDoesNotMatchPDG
  ∷ missingCertifiedDiagonalisation
  ∷ []

data PhysicalMassMatrixPromotion : Set where

physicalMassMatrixPromotionImpossibleHere :
  PhysicalMassMatrixPromotion →
  ⊥
physicalMassMatrixPromotionImpossibleHere ()

record PhysicalMassMatrixReceipt : Set where
  field
    status :
      PhysicalMassMatrixStatus

    osCorrectionReceipt :
      OS.OSPositivityDissolvedReceipt

    osCorrectionReceiptIsCanonical :
      osCorrectionReceipt ≡ OS.canonicalOSPositivityDissolvedReceipt

    y13Receipt :
      Y13.Y13ComplexEntryReceipt

    y13ReceiptIsCanonical :
      y13Receipt ≡ Y13.canonicalY13ComplexEntryReceipt

    diagnosticScript :
      String

    vevGeVPDGInput :
      Float

    scaleVOverSqrt2GeV :
      Float

    mdEigenvalueGeV :
      Float

    msEigenvalueGeV :
      Float

    mbEigenvalueGeV :
      Float

    mdOverPDG :
      Float

    msOverPDG :
      Float

    mbOverPDG :
      Float

    physicalMassEigenvaluesComputed :
      Bool

    physicalMassEigenvaluesComputedIsTrue :
      physicalMassEigenvaluesComputed ≡ true

    physicalHamiltonianPSDByConstruction :
      Bool

    physicalHamiltonianPSDByConstructionIsTrue :
      physicalHamiltonianPSDByConstruction ≡ true

    physicalMassMatchesPDG :
      Bool

    physicalMassMatchesPDGIsFalse :
      physicalMassMatchesPDG ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List PhysicalMassMatrixBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPhysicalMassMatrixBlockers

    promotionFlags :
      List PhysicalMassMatrixPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open PhysicalMassMatrixReceipt public

canonicalPhysicalMassMatrixReceipt :
  PhysicalMassMatrixReceipt
canonicalPhysicalMassMatrixReceipt =
  record
    { status =
        pdgVEVCalibratedMassMatrixDiagnosticRecorded
    ; osCorrectionReceipt =
        OS.canonicalOSPositivityDissolvedReceipt
    ; osCorrectionReceiptIsCanonical =
        refl
    ; y13Receipt =
        Y13.canonicalY13ComplexEntryReceipt
    ; y13ReceiptIsCanonical =
        refl
    ; diagnosticScript =
        "scripts/check_physical_mass_matrix.py"
    ; vevGeVPDGInput =
        246.22
    ; scaleVOverSqrt2GeV =
        174.10383166375172
    ; mdEigenvalueGeV =
        0.013417368926335067
    ; msEigenvalueGeV =
        7.147906264153982
    ; mbEigenvalueGeV =
        59.68673185385159
    ; mdOverPDG =
        2.873098271163826
    ; msOverPDG =
        76.53004565475356
    ; mbOverPDG =
        14.279122453074544
    ; physicalMassEigenvaluesComputed =
        true
    ; physicalMassEigenvaluesComputedIsTrue =
        refl
    ; physicalHamiltonianPSDByConstruction =
        true
    ; physicalHamiltonianPSDByConstructionIsTrue =
        refl
    ; physicalMassMatchesPDG =
        false
    ; physicalMassMatchesPDGIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalPhysicalMassMatrixBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The PDG VEV-calibrated mass matrix is numerically evaluated"
        ∷ "The diagnostic masses are [0.0134, 7.148, 59.687] GeV and do not match down-quark PDG targets"
        ∷ "The PSD Hamiltonian observation is retained, but no physical mass or CKM claim is promoted"
        ∷ []
    }

physicalMassMatrixComputedButNotMatched :
  physicalMassMatchesPDG canonicalPhysicalMassMatrixReceipt ≡ false
physicalMassMatrixComputedButNotMatched =
  refl

