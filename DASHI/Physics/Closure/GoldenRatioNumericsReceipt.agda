module DASHI.Physics.Closure.GoldenRatioNumericsReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.VubVtdFromFullCKM as Prior

------------------------------------------------------------------------
-- Golden-ratio corrected CKM-tail diagnostic.
--
-- This receipt records the numerical check requested for the phi-corrected
-- 1-3 Yukawa magnitude.  The requested C1 formula uses the 14-degree
-- p3-p5 resummed factor in the 1-3 channel.  With that convention it improves
-- the Jarlskog overshoot substantially but undershoots |Vub|; this is kept as
-- a diagnostic, not as a physical CKM derivation.

data GoldenRatioNumericsStatus : Set where
  goldenRatioNumericalDiagnosticRecorded :
    GoldenRatioNumericsStatus

data GoldenRatioNumericsBlocker : Set where
  y13NormalisationStillOpen :
    GoldenRatioNumericsBlocker

  heckePhaseNotPhysicalCKMPhase :
    GoldenRatioNumericsBlocker

  noCertifiedPhysicalEigenbasis :
    GoldenRatioNumericsBlocker

  jarlskogStillBelowPDGSizedTarget :
    GoldenRatioNumericsBlocker

canonicalGoldenRatioNumericsBlockers :
  List GoldenRatioNumericsBlocker
canonicalGoldenRatioNumericsBlockers =
  y13NormalisationStillOpen
  ∷ heckePhaseNotPhysicalCKMPhase
  ∷ noCertifiedPhysicalEigenbasis
  ∷ jarlskogStillBelowPDGSizedTarget
  ∷ []

data GoldenRatioNumericsPromotion : Set where

goldenRatioNumericsPromotionImpossibleHere :
  GoldenRatioNumericsPromotion →
  ⊥
goldenRatioNumericsPromotionImpossibleHere ()

record GoldenRatioNumericsReceipt : Set where
  field
    status :
      GoldenRatioNumericsStatus

    priorJarlskogReceipt :
      Prior.VubVtdFromFullCKMReceipt

    priorJarlskogReceiptIsCanonical :
      priorJarlskogReceipt ≡ Prior.canonicalVubVtdFromFullCKMReceipt

    formula :
      String

    alphaOne :
      Float

    phi :
      Float

    y13PhiCorrected :
      Float

    vubPhiCorrected :
      Float

    pdgVubTarget :
      Float

    vubPhiOverPDG :
      Float

    vubRelativeError :
      Float

    lambdaCarrier :
      Float

    vcbGeometricCarrier :
      Float

    wolfensteinAGeometricCarrier :
      Float

    delta29 :
      Float

    jarlskogPhiCorrected :
      Float

    pdgJarlskogTarget :
      Float

    jarlskogPhiOverPDG :
      Float

    jarlskogGoldenRatioCorrected :
      Bool

    jarlskogGoldenRatioCorrectedIsDiagnostic :
      jarlskogGoldenRatioCorrected ≡ true

    vubPDGMatched :
      Bool

    vubPDGMatchedIsFalse :
      vubPDGMatched ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalPromotionConstructed :
      Bool

    terminalPromotionConstructedIsFalse :
      terminalPromotionConstructed ≡ false

    blockers :
      List GoldenRatioNumericsBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGoldenRatioNumericsBlockers

    promotionFlags :
      List GoldenRatioNumericsPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open GoldenRatioNumericsReceipt public

canonicalGoldenRatioNumericsReceipt :
  GoldenRatioNumericsReceipt
canonicalGoldenRatioNumericsReceipt =
  record
    { status =
        goldenRatioNumericalDiagnosticRecorded
    ; priorJarlskogReceipt =
        Prior.canonicalVubVtdFromFullCKMReceipt
    ; priorJarlskogReceiptIsCanonical =
        refl
    ; formula =
        "phi=(1+sqrt5)/2; y13_phi = phi * 14/(1-alpha1/2) * vol(X0(7))/sqrt24 with vol(X0(7))=8*pi/3; |Vub|_phi = alpha1^3 * y13_phi"
    ; alphaOne =
        0.04124
    ; phi =
        1.618033988749895
    ; y13PhiCorrected =
        39.5528178297048
    ; vubPhiCorrected =
        0.002774172094698646
    ; pdgVubTarget =
        0.00369
    ; vubPhiOverPDG =
        0.7518081557448906
    ; vubRelativeError =
        -0.24819184425510948
    ; lambdaCarrier =
        0.2244032573430574
    ; vcbGeometricCarrier =
        0.04071724010722473
    ; wolfensteinAGeometricCarrier =
        0.8085744605386272
    ; delta29 =
        1.003510488600938
    ; jarlskogPhiCorrected =
        0.000020832213223275858
    ; pdgJarlskogTarget =
        0.0000308
    ; jarlskogPhiOverPDG =
        0.6763705591972681
    ; jarlskogGoldenRatioCorrected =
        true
    ; jarlskogGoldenRatioCorrectedIsDiagnostic =
        refl
    ; vubPDGMatched =
        false
    ; vubPDGMatchedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalPromotionConstructed =
        false
    ; terminalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalGoldenRatioNumericsBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The phi-corrected C1 convention lowers the Jarlskog diagnostic from 11.26x PDG to about 0.676x PDG"
        ∷ "The same convention undershoots |Vub| by about 24.8 percent"
        ∷ "The |Vub|_phi / PDG |Vub| ratio is approximately 0.7518"
        ∷ "This is a useful diagnostic, not a physical CKM or terminal promotion"
        ∷ []
    }

goldenRatioNumericsDoesNotPromoteCKM :
  physicalCKMPromoted canonicalGoldenRatioNumericsReceipt ≡ false
goldenRatioNumericsDoesNotPromoteCKM =
  refl

goldenRatioNumericsNoTerminalPromotion :
  terminalPromotionConstructed canonicalGoldenRatioNumericsReceipt ≡ false
goldenRatioNumericsNoTerminalPromotion =
  refl
