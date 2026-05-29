module DASHI.Physics.Closure.Deg23FaltingsComputationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FaltingsHeightDeg23Receipt as Route

------------------------------------------------------------------------
-- Numerical Faltings-height diagnostic for the deg23 residual.

data Deg23FaltingsComputationStatus : Set where
  faltingsNumericalComputationRecorded :
    Deg23FaltingsComputationStatus

data Deg23FaltingsComputationBlocker : Set where
  correctionOvershootsResidual :
    Deg23FaltingsComputationBlocker

  missingCertifiedLDerivativeEvaluation :
    Deg23FaltingsComputationBlocker

  missingCorrectPhysicalNormalisation :
    Deg23FaltingsComputationBlocker

canonicalDeg23FaltingsComputationBlockers :
  List Deg23FaltingsComputationBlocker
canonicalDeg23FaltingsComputationBlockers =
  correctionOvershootsResidual
  ∷ missingCertifiedLDerivativeEvaluation
  ∷ missingCorrectPhysicalNormalisation
  ∷ []

data Deg23FaltingsPromotion : Set where

deg23FaltingsPromotionImpossibleHere :
  Deg23FaltingsPromotion →
  ⊥
deg23FaltingsPromotionImpossibleHere ()

record Deg23FaltingsComputationReceipt : Set where
  field
    status :
      Deg23FaltingsComputationStatus

    routeReceipt :
      Route.FaltingsHeightDeg23Receipt

    routeReceiptIsCanonical :
      routeReceipt ≡ Route.canonicalFaltingsHeightDeg23Receipt

    computationScript :
      String

    formulaLabel :
      String

    hMinusThreeDiagnostic :
      Float

    hMinusThreeLabel :
      String

    hMinusSevenDiagnostic :
      Float

    hMinusSevenLabel :
      String

    deltaHeight :
      Float

    deltaHeightLabel :
      String

    expTwoDeltaHeight :
      Float

    expTwoDeltaHeightLabel :
      String

    correctedDeg23 :
      Float

    correctedDeg23Label :
      String

    requiredDeg23 :
      Float

    requiredDeg23Label :
      String

    faltingsNumericalComputationRecordedFlag :
      Bool

    faltingsNumericalComputationRecordedFlagIsTrue :
      faltingsNumericalComputationRecordedFlag ≡ true

    faltingsCorrectionResolvesDeg23Residual :
      Bool

    faltingsCorrectionResolvesDeg23ResidualIsFalse :
      faltingsCorrectionResolvesDeg23Residual ≡ false

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    blockers :
      List Deg23FaltingsComputationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23FaltingsComputationBlockers

    promotionFlags :
      List Deg23FaltingsPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23FaltingsComputationReceipt public

canonicalDeg23FaltingsComputationReceipt :
  Deg23FaltingsComputationReceipt
canonicalDeg23FaltingsComputationReceipt =
  record
    { status =
        faltingsNumericalComputationRecorded
    ; routeReceipt =
        Route.canonicalFaltingsHeightDeg23Receipt
    ; routeReceiptIsCanonical =
        refl
    ; computationScript =
        "scripts/check_deg23_faltings.py"
    ; formulaLabel =
        "h_F(D)=-(1/2)log|D|+(1/2)(L'/L)(1,chi_D)-(1/2)log(2*pi)"
    ; hMinusThreeDiagnostic =
        -1.284103869558579
    ; hMinusThreeLabel =
        "h_F(D=-3) ~= -1.28410386956 under the recorded normalisation"
    ; hMinusSevenDiagnostic =
        -1.8840757627356555
    ; hMinusSevenLabel =
        "h_F(D=-7) ~= -1.88407576274 under the recorded normalisation"
    ; deltaHeight =
        0.5999718931770766
    ; deltaHeightLabel =
        "h_F(-3)-h_F(-7) ~= 0.59997189318"
    ; expTwoDeltaHeight =
        3.319930292105326
    ; expTwoDeltaHeightLabel =
        "exp(2*(h_F(-3)-h_F(-7))) ~= 3.3199302921"
    ; correctedDeg23 =
        46.479024089474564
    ; correctedDeg23Label =
        "14 * exp(2*Delta h) ~= 46.479, not 14.302"
    ; requiredDeg23 =
        14.302
    ; requiredDeg23Label =
        "required diagnostic deg23 remains 14.302"
    ; faltingsNumericalComputationRecordedFlag =
        true
    ; faltingsNumericalComputationRecordedFlagIsTrue =
        refl
    ; faltingsCorrectionResolvesDeg23Residual =
        false
    ; faltingsCorrectionResolvesDeg23ResidualIsFalse =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23FaltingsComputationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The direct Faltings-height correction test overshoots the 2.1 percent residual"
        ∷ "This closes the naive Faltings route as a negative diagnostic"
        ∷ "The correct deg23 normalisation remains open; Vcb is not promoted"
        ∷ []
    }

deg23FaltingsComputationIsRecorded :
  faltingsNumericalComputationRecordedFlag canonicalDeg23FaltingsComputationReceipt ≡ true
deg23FaltingsComputationIsRecorded =
  refl

deg23FaltingsDoesNotPromoteVcb :
  physicalVcbPromoted canonicalDeg23FaltingsComputationReceipt ≡ false
deg23FaltingsDoesNotPromoteVcb =
  refl

