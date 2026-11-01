module DASHI.Physics.Closure.Y13MagnitudeCorrectionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Y13FromBridgeIsogenyReceipt as Y13
import DASHI.Physics.Closure.JarlskogDiagnosticAnalysis as J

------------------------------------------------------------------------
-- Golden-ratio magnitude diagnostic for the y13 bridge entry.

data Y13MagnitudeCorrectionStatus : Set where
  y13GoldenRatioMagnitudeDiagnosticRecorded :
    Y13MagnitudeCorrectionStatus

data Y13MagnitudeCorrectionBlocker : Set where
  missingGoldenRatioDerivationFromCarrier :
    Y13MagnitudeCorrectionBlocker

  missingPhysicalVubAuthority :
    Y13MagnitudeCorrectionBlocker

  missingCorrectPhysicalEigenbasis :
    Y13MagnitudeCorrectionBlocker

canonicalY13MagnitudeCorrectionBlockers :
  List Y13MagnitudeCorrectionBlocker
canonicalY13MagnitudeCorrectionBlockers =
  missingGoldenRatioDerivationFromCarrier
  ∷ missingPhysicalVubAuthority
  ∷ missingCorrectPhysicalEigenbasis
  ∷ []

data Y13MagnitudeCorrectionPromotion : Set where

y13MagnitudeCorrectionPromotionImpossibleHere :
  Y13MagnitudeCorrectionPromotion →
  ⊥
y13MagnitudeCorrectionPromotionImpossibleHere ()

record Y13MagnitudeCorrectionReceipt : Set where
  field
    status :
      Y13MagnitudeCorrectionStatus

    y13BridgeReceipt :
      Y13.Y13FromBridgeIsogenyReceipt

    y13BridgeReceiptIsCanonical :
      y13BridgeReceipt ≡ Y13.canonicalY13FromBridgeIsogenyReceipt

    jarlskogAnalysisReceipt :
      J.JarlskogDiagnosticAnalysisReceipt

    jarlskogAnalysisReceiptIsCanonical :
      jarlskogAnalysisReceipt ≡ J.canonicalJarlskogDiagnosticAnalysisReceipt

    phiLabel :
      String

    currentY13Magnitude :
      Float

    requiredY13ForLowVubTarget :
      Float

    requiredOverCurrent :
      Float

    requiredOverPhiCurrent :
      Float

    phiCorrectedY13 :
      Float

    y13GoldenRatioFactor :
      Bool

    y13GoldenRatioFactorIsTrue :
      y13GoldenRatioFactor ≡ true

    goldenRatioCarrierDerived :
      Bool

    goldenRatioCarrierDerivedIsFalse :
      goldenRatioCarrierDerived ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Y13MagnitudeCorrectionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalY13MagnitudeCorrectionBlockers

    promotionFlags :
      List Y13MagnitudeCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Y13MagnitudeCorrectionReceipt public

canonicalY13MagnitudeCorrectionReceipt :
  Y13MagnitudeCorrectionReceipt
canonicalY13MagnitudeCorrectionReceipt =
  record
    { status =
        y13GoldenRatioMagnitudeDiagnosticRecorded
    ; y13BridgeReceipt =
        Y13.canonicalY13FromBridgeIsogenyReceipt
    ; y13BridgeReceiptIsCanonical =
        refl
    ; jarlskogAnalysisReceipt =
        J.canonicalJarlskogDiagnosticAnalysisReceipt
    ; jarlskogAnalysisReceiptIsCanonical =
        refl
    ; phiLabel =
        "phi = (1 + sqrt(5))/2 ~= 1.618033988749895"
    ; currentY13Magnitude =
        30.781195923884738
    ; requiredY13ForLowVubTarget =
        50.89935116926654
    ; requiredOverCurrent =
        1.6535858871477787
    ; requiredOverPhiCurrent =
        1.0219722815744752
    ; phiCorrectedY13 =
        49.805021219215234
    ; y13GoldenRatioFactor =
        true
    ; y13GoldenRatioFactorIsTrue =
        refl
    ; goldenRatioCarrierDerived =
        false
    ; goldenRatioCarrierDerivedIsFalse =
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
        canonicalY13MagnitudeCorrectionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The required low-|Vub| y13 correction is near phi but still off by about 2.2 percent"
        ∷ "The phi factor is recorded as a diagnostic hypothesis, not a derivation"
        ∷ "No physical Vub or CKM promotion is asserted"
        ∷ []
    }

