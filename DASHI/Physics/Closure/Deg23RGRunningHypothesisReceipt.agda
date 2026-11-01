module DASHI.Physics.Closure.Deg23RGRunningHypothesisReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt as Deg23

------------------------------------------------------------------------
-- QCD running diagnostic for the p3-p5 degree residual.

data Deg23RGRunningHypothesisStatus : Set where
  oneLoopQCDRunningDiagnosticRecorded :
    Deg23RGRunningHypothesisStatus

data Deg23RGRunningBlocker : Set where
  oneLoopRunningOvershootsTwoPercent :
    Deg23RGRunningBlocker

  missingCarrierScale :
    Deg23RGRunningBlocker

  missingThresholdMatchedAuthority :
    Deg23RGRunningBlocker

canonicalDeg23RGRunningBlockers :
  List Deg23RGRunningBlocker
canonicalDeg23RGRunningBlockers =
  oneLoopRunningOvershootsTwoPercent
  ∷ missingCarrierScale
  ∷ missingThresholdMatchedAuthority
  ∷ []

data Deg23RGRunningPromotion : Set where

deg23RGRunningPromotionImpossibleHere :
  Deg23RGRunningPromotion →
  ⊥
deg23RGRunningPromotionImpossibleHere ()

record Deg23RGRunningHypothesisReceipt : Set where
  field
    status :
      Deg23RGRunningHypothesisStatus

    residualReceipt :
      Deg23.Deg23ResidualDiagnosticReceipt

    residualReceiptIsCanonical :
      residualReceipt ≡ Deg23.canonicalDeg23ResidualDiagnosticReceipt

    diagnosticScript :
      String

    targetCorrection :
      Float

    targetPercent :
      Float

    naturalP5P7OneLoopCorrection :
      Float

    naturalP5P7OneLoopCorrectionLabel :
      String

    naturalP5P7DistanceFromTarget :
      Float

    tunedHighScaleGeV :
      Float

    rgRunningDiagnosticRecorded :
      Bool

    rgRunningDiagnosticRecordedIsTrue :
      rgRunningDiagnosticRecorded ≡ true

    naturalP5P7RunningResolvesResidual :
      Bool

    naturalP5P7RunningResolvesResidualIsFalse :
      naturalP5P7RunningResolvesResidual ≡ false

    rgRunningHypothesisClosed :
      Bool

    rgRunningHypothesisClosedIsFalse :
      rgRunningHypothesisClosed ≡ false

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    blockers :
      List Deg23RGRunningBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23RGRunningBlockers

    promotionFlags :
      List Deg23RGRunningPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23RGRunningHypothesisReceipt public

canonicalDeg23RGRunningHypothesisReceipt :
  Deg23RGRunningHypothesisReceipt
canonicalDeg23RGRunningHypothesisReceipt =
  record
    { status =
        oneLoopQCDRunningDiagnosticRecorded
    ; residualReceipt =
        Deg23.canonicalDeg23ResidualDiagnosticReceipt
    ; residualReceiptIsCanonical =
        refl
    ; diagnosticScript =
        "scripts/check_deg23_rg_running.py"
    ; targetCorrection =
        1.0215714285714286
    ; targetPercent =
        2.1571428571428575
    ; naturalP5P7OneLoopCorrection =
        1.0426026539911517
    ; naturalP5P7OneLoopCorrectionLabel =
        "Natural p5 -> p7 scale test gives about 4.26%, overshooting the required 2.16%"
    ; naturalP5P7DistanceFromTarget =
        0.021031225419723095
    ; tunedHighScaleGeV =
        5.9191879997904016
    ; rgRunningDiagnosticRecorded =
        true
    ; rgRunningDiagnosticRecordedIsTrue =
        refl
    ; naturalP5P7RunningResolvesResidual =
        false
    ; naturalP5P7RunningResolvesResidualIsFalse =
        refl
    ; rgRunningHypothesisClosed =
        false
    ; rgRunningHypothesisClosedIsFalse =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23RGRunningBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "A one-loop QCD running scan was performed as a deg23 residual diagnostic"
        ∷ "The natural p5 -> p7 scale correction is 4.26 percent, not the required 2.16 percent"
        ∷ "A tuned scale near 5.919 GeV can reproduce the factor, but that is not a carrier derivation"
        ∷ "The deg23 residual and physical Vcb promotion remain open"
        ∷ []
    }

deg23RGRunningDoesNotResolveResidual :
  naturalP5P7RunningResolvesResidual canonicalDeg23RGRunningHypothesisReceipt ≡ false
deg23RGRunningDoesNotResolveResidual =
  refl
