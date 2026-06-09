module DASHI.Physics.Closure.NSTailRestrictedThetaDiagnosticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as Negative
import DASHI.Physics.Closure.NSThetaPressureMarginCorrectionReceipt as Correction

------------------------------------------------------------------------
-- Tail-restricted theta diagnostic receipt.
--
-- The latest theta sweep shows that the global theta maximum is dominated by
-- the low shell k=2 in every tested trace.  That is not the dissipative tail
-- seam used by the Clay-facing tail absorption theorem.  This receipt records
-- the corrected diagnostic split:
--
--   Theta_global = sup over all shells.
--   Theta_tail   = sup over shells k >= K_diss(nu).
--
-- The tail-restricted quantity is the one consumed by the pressure-margin
-- route.  The global low-shell maximum is a warning signal, not a Clay seam.

data NSTailRestrictedThetaDiagnosticStatus : Set where
  tailRestrictedThetaDiagnosticRecorded_noPromotion :
    NSTailRestrictedThetaDiagnosticStatus

data ThetaDiagnosticSplit : Set where
  thetaGlobalIsAllShellSupremum :
    ThetaDiagnosticSplit

  thetaTailIsDissipativeTailSupremum :
    ThetaDiagnosticSplit

  globalDangerShellAtKTwoIsLowModeWarning :
    ThetaDiagnosticSplit

  claySeamUsesTailRestrictedTheta :
    ThetaDiagnosticSplit

canonicalThetaDiagnosticSplit :
  List ThetaDiagnosticSplit
canonicalThetaDiagnosticSplit =
  thetaGlobalIsAllShellSupremum
  ∷ thetaTailIsDissipativeTailSupremum
  ∷ globalDangerShellAtKTwoIsLowModeWarning
  ∷ claySeamUsesTailRestrictedTheta
  ∷ []

data TailThetaTraceDatum : Set where
  smoothTailThetaPasses :
    TailThetaTraceDatum

  kolmogorovTailThetaPasses :
    TailThetaTraceDatum

  nearCriticalTailThetaFails :
    TailThetaTraceDatum

  roughTailThetaFails :
    TailThetaTraceDatum

  inviscidTailUnavailableAtKmax64 :
    TailThetaTraceDatum

canonicalTailThetaTraceData :
  List TailThetaTraceDatum
canonicalTailThetaTraceData =
  smoothTailThetaPasses
  ∷ kolmogorovTailThetaPasses
  ∷ nearCriticalTailThetaFails
  ∷ roughTailThetaFails
  ∷ inviscidTailUnavailableAtKmax64
  ∷ []

data TailRestrictedThetaOpenObligation : Set where
  rerunDiagnosticsWithThetaGlobalAndThetaTail :
    TailRestrictedThetaOpenObligation

  proveTailRestrictedThetaBarrier :
    TailRestrictedThetaOpenObligation

  proveNegativeSobolevDefectBoundOnTail :
    TailRestrictedThetaOpenObligation

  proveNoLowModeRepresentationGrowthLeaksIntoTailSeam :
    TailRestrictedThetaOpenObligation

canonicalTailRestrictedThetaOpenObligations :
  List TailRestrictedThetaOpenObligation
canonicalTailRestrictedThetaOpenObligations =
  rerunDiagnosticsWithThetaGlobalAndThetaTail
  ∷ proveTailRestrictedThetaBarrier
  ∷ proveNegativeSobolevDefectBoundOnTail
  ∷ proveNoLowModeRepresentationGrowthLeaksIntoTailSeam
  ∷ []

data NSTailRestrictedThetaPromotion : Set where

nsTailRestrictedThetaPromotionImpossibleHere :
  NSTailRestrictedThetaPromotion →
  ⊥
nsTailRestrictedThetaPromotionImpossibleHere ()

smoothTailThetaMillionths :
  Nat
smoothTailThetaMillionths =
  3990

kolmogorovTailThetaMillionths :
  Nat
kolmogorovTailThetaMillionths =
  318840

nearCriticalTailThetaMillionths :
  Nat
nearCriticalTailThetaMillionths =
  2015900

roughTailThetaMillionths :
  Nat
roughTailThetaMillionths =
  2763000

globalDangerShell :
  Nat
globalDangerShell =
  2

inviscidKDiss :
  Nat
inviscidKDiss =
  178

diagnosticSplitStatement :
  String
diagnosticSplitStatement =
  "Theta_global is dominated by low k=2 on the sweep; the Clay-facing tail theorem must consume Theta_tail = sup_{k >= K_diss(nu)} theta(k), not the all-shell supremum."

traceStatement :
  String
traceStatement =
  "Tail-restricted sweep: smooth theta_tail=0.00399, Kolmogorov=0.31884, near-critical=2.0159, rough=2.7630, inviscid has no tail data at kmax=64 because K_diss=178."

promotionBoundary :
  String
promotionBoundary =
  "This receipt corrects the theta diagnostic surface only.  It does not prove the tail barrier, the H^{-1/2} nonlinear-defect bound, NS regularity, or Clay Navier-Stokes."

record NSTailRestrictedThetaDiagnosticReceipt : Setω where
  field
    status :
      NSTailRestrictedThetaDiagnosticStatus

    statusIsCanonical :
      status ≡ tailRestrictedThetaDiagnosticRecorded_noPromotion

    pressureCorrectionReceipt :
      Correction.NSThetaPressureMarginCorrectionReceipt

    pressureCorrectionNoClay :
      Correction.clayNavierStokesPromoted pressureCorrectionReceipt ≡ false

    negativeSobolevReceipt :
      Negative.NSNegativeSobolevDangerShellReceipt zero

    negativeSobolevDefectStillOpen :
      Negative.highHighDefectBoundProvedHere negativeSobolevReceipt ≡ false

    negativeSobolevNoClay :
      Negative.clayNavierStokesPromoted negativeSobolevReceipt ≡ false

    diagnosticSplit :
      List ThetaDiagnosticSplit

    diagnosticSplitIsCanonical :
      diagnosticSplit ≡ canonicalThetaDiagnosticSplit

    traceData :
      List TailThetaTraceDatum

    traceDataAreCanonical :
      traceData ≡ canonicalTailThetaTraceData

    openObligations :
      List TailRestrictedThetaOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalTailRestrictedThetaOpenObligations

    globalDangerShellRecorded :
      Nat

    globalDangerShellIsKTwo :
      globalDangerShellRecorded ≡ globalDangerShell

    smoothTailTheta :
      Nat

    smoothTailThetaIs000399 :
      smoothTailTheta ≡ smoothTailThetaMillionths

    kolmogorovTailTheta :
      Nat

    kolmogorovTailThetaIs031884 :
      kolmogorovTailTheta ≡ kolmogorovTailThetaMillionths

    nearCriticalTailTheta :
      Nat

    nearCriticalTailThetaIs20159 :
      nearCriticalTailTheta ≡ nearCriticalTailThetaMillionths

    roughTailTheta :
      Nat

    roughTailThetaIs2763 :
      roughTailTheta ≡ roughTailThetaMillionths

    inviscidKDissRecorded :
      Nat

    inviscidKDissIs178 :
      inviscidKDissRecorded ≡ inviscidKDiss

    thetaGlobalUsedForClaySeam :
      Bool

    thetaGlobalUsedForClaySeamIsFalse :
      thetaGlobalUsedForClaySeam ≡ false

    thetaTailIsClayDiagnostic :
      Bool

    thetaTailIsClayDiagnosticIsTrue :
      thetaTailIsClayDiagnostic ≡ true

    tailRestrictedBarrierProvedHere :
      Bool

    tailRestrictedBarrierProvedHereIsFalse :
      tailRestrictedBarrierProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSTailRestrictedThetaPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSTailRestrictedThetaPromotion →
      ⊥

    diagnosticText :
      String

    diagnosticTextIsCanonical :
      diagnosticText ≡ diagnosticSplitStatement

    traceText :
      String

    traceTextIsCanonical :
      traceText ≡ traceStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open NSTailRestrictedThetaDiagnosticReceipt public

canonicalNSTailRestrictedThetaDiagnosticReceipt :
  NSTailRestrictedThetaDiagnosticReceipt
canonicalNSTailRestrictedThetaDiagnosticReceipt =
  record
    { status =
        tailRestrictedThetaDiagnosticRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; pressureCorrectionReceipt =
        Correction.canonicalNSThetaPressureMarginCorrectionReceipt
    ; pressureCorrectionNoClay =
        refl
    ; negativeSobolevReceipt =
        Negative.canonicalNSNegativeSobolevDangerShellReceipt
    ; negativeSobolevDefectStillOpen =
        refl
    ; negativeSobolevNoClay =
        refl
    ; diagnosticSplit =
        canonicalThetaDiagnosticSplit
    ; diagnosticSplitIsCanonical =
        refl
    ; traceData =
        canonicalTailThetaTraceData
    ; traceDataAreCanonical =
        refl
    ; openObligations =
        canonicalTailRestrictedThetaOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; globalDangerShellRecorded =
        globalDangerShell
    ; globalDangerShellIsKTwo =
        refl
    ; smoothTailTheta =
        smoothTailThetaMillionths
    ; smoothTailThetaIs000399 =
        refl
    ; kolmogorovTailTheta =
        kolmogorovTailThetaMillionths
    ; kolmogorovTailThetaIs031884 =
        refl
    ; nearCriticalTailTheta =
        nearCriticalTailThetaMillionths
    ; nearCriticalTailThetaIs20159 =
        refl
    ; roughTailTheta =
        roughTailThetaMillionths
    ; roughTailThetaIs2763 =
        refl
    ; inviscidKDissRecorded =
        inviscidKDiss
    ; inviscidKDissIs178 =
        refl
    ; thetaGlobalUsedForClaySeam =
        false
    ; thetaGlobalUsedForClaySeamIsFalse =
        refl
    ; thetaTailIsClayDiagnostic =
        true
    ; thetaTailIsClayDiagnosticIsTrue =
        refl
    ; tailRestrictedBarrierProvedHere =
        false
    ; tailRestrictedBarrierProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsTailRestrictedThetaPromotionImpossibleHere
    ; diagnosticText =
        diagnosticSplitStatement
    ; diagnosticTextIsCanonical =
        refl
    ; traceText =
        traceStatement
    ; traceTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSTailThetaUsesTailNotGlobal :
  thetaGlobalUsedForClaySeam canonicalNSTailRestrictedThetaDiagnosticReceipt
  ≡
  false
canonicalNSTailThetaUsesTailNotGlobal =
  refl

canonicalNSTailThetaNoClay :
  clayNavierStokesPromoted canonicalNSTailRestrictedThetaDiagnosticReceipt
  ≡
  false
canonicalNSTailThetaNoClay =
  refl
