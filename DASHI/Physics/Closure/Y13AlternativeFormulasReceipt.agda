module DASHI.Physics.Closure.Y13AlternativeFormulasReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Y13MagnitudeCorrectionReceipt as Phi
import DASHI.Physics.Closure.Y13FromP5ReductionReceipt as P5

------------------------------------------------------------------------
-- Systematic y13 formula comparison table.

data Y13AlternativeStatus : Set where
  y13AlternativeFormulaTableRecorded :
    Y13AlternativeStatus

data Y13AlternativeBlocker : Set where
  requestedPhiFourteenFormulaDoesNotGiveClaimedAccuracy :
    Y13AlternativeBlocker

  missingGoldenRatioDerivation :
    Y13AlternativeBlocker

  missingPhysicalVubAuthority :
    Y13AlternativeBlocker

canonicalY13AlternativeBlockers :
  List Y13AlternativeBlocker
canonicalY13AlternativeBlockers =
  requestedPhiFourteenFormulaDoesNotGiveClaimedAccuracy
  ∷ missingGoldenRatioDerivation
  ∷ missingPhysicalVubAuthority
  ∷ []

data Y13AlternativePromotion : Set where

y13AlternativePromotionImpossibleHere :
  Y13AlternativePromotion →
  ⊥
y13AlternativePromotionImpossibleHere ()

record Y13AlternativeFormulasReceipt : Set where
  field
    status :
      Y13AlternativeStatus

    phiCorrectionReceipt :
      Phi.Y13MagnitudeCorrectionReceipt

    phiCorrectionReceiptIsCanonical :
      phiCorrectionReceipt ≡ Phi.canonicalY13MagnitudeCorrectionReceipt

    p5ReductionReceipt :
      P5.Y13FromP5ReductionReceipt

    p5ReductionReceiptIsCanonical :
      p5ReductionReceipt ≡ P5.canonicalY13FromP5ReductionReceipt

    bridgeY13 :
      Float

    bridgeRelativeErrorAgainstPDGVub :
      Float

    bridgePhiY13 :
      Float

    bridgePhiRelativeErrorAgainstPDGVub :
      Float

    bridgePhiSquaredY13 :
      Float

    bridgePhiSquaredRelativeErrorAgainstPDGVub :
      Float

    bridgeGeometricY13 :
      Float

    bridgeGeometricRelativeErrorAgainstPDGVub :
      Float

    requestedPhiFourteenGeometricY13 :
      Float

    requestedPhiFourteenRelativeErrorAgainstPDGVub :
      Float

    bestCurrentDiagnosticFormula :
      String

    bestCurrentDiagnosticRelativeErrorAgainstLowVub :
      Float

    vubAlternativeTableRecorded :
      Bool

    vubAlternativeTableRecordedIsTrue :
      vubAlternativeTableRecorded ≡ true

    requestedBestFormulaMatchesClaimedAccuracy :
      Bool

    requestedBestFormulaMatchesClaimedAccuracyIsFalse :
      requestedBestFormulaMatchesClaimedAccuracy ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Y13AlternativeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalY13AlternativeBlockers

    promotionFlags :
      List Y13AlternativePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Y13AlternativeFormulasReceipt public

canonicalY13AlternativeFormulasReceipt :
  Y13AlternativeFormulasReceipt
canonicalY13AlternativeFormulasReceipt =
  record
    { status =
        y13AlternativeFormulaTableRecorded
    ; phiCorrectionReceipt =
        Phi.canonicalY13MagnitudeCorrectionReceipt
    ; phiCorrectionReceiptIsCanonical =
        refl
    ; p5ReductionReceipt =
        P5.canonicalY13FromP5ReductionReceipt
    ; p5ReductionReceiptIsCanonical =
        refl
    ; bridgeY13 =
        30.781195923884738
    ; bridgeRelativeErrorAgainstPDGVub =
        -0.41492021532336326
    ; bridgePhiY13 =
        49.805021219215234
    ; bridgePhiRelativeErrorAgainstPDGVub =
        -0.053321022262731846
    ; bridgePhiSquaredY13 =
        80.58621714309996
    ; bridgePhiSquaredRelativeErrorAgainstPDGVub =
        0.531758762413905
    ; bridgeGeometricY13 =
        31.429267418044816
    ; bridgeGeometricRelativeErrorAgainstPDGVub =
        -0.40260186579607843
    ; requestedPhiFourteenGeometricY13 =
        39.5528178297048
    ; requestedPhiFourteenRelativeErrorAgainstPDGVub =
        -0.24819184425510948
    ; bestCurrentDiagnosticFormula =
        "Among checked formulas, bridge*phi is closest to the PDG |Vub| target; the requested phi*14/(1-alpha1/2) formula undershoots by about 24.8 percent"
    ; bestCurrentDiagnosticRelativeErrorAgainstLowVub =
        -0.02149988015391602
    ; vubAlternativeTableRecorded =
        true
    ; vubAlternativeTableRecordedIsTrue =
        refl
    ; requestedBestFormulaMatchesClaimedAccuracy =
        false
    ; requestedBestFormulaMatchesClaimedAccuracyIsFalse =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalY13AlternativeBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The formula table is a diagnostic sweep, not a derivation"
        ∷ "The requested phi*14 geometric formula is numerically inconsistent with the claimed 0.16 percent Vub accuracy"
        ∷ "No physical Vub or CKM promotion is asserted"
        ∷ []
    }

