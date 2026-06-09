module DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.KPCouplingObstructionReceipt as KPC
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt as Actual

------------------------------------------------------------------------
-- YM Balaban RG scale-transfer frontier.
--
-- This is YM6 in the Paper 3 roadmap.  It records why perturbative beta
-- bookkeeping does not reach the strict KP absorption threshold, and why a
-- nonperturbative Balaban block-spin transfer remains the hard open step.

data YMBalabanRGScaleTransferStatus : Set where
  balabanRGScaleTransferFrontierRecorded :
    YMBalabanRGScaleTransferStatus

data YMBetaEstimateVerdict : Set where
  oneLoopBelowStrictKPMargin :
    YMBetaEstimateVerdict

  twoLoopBelowStrictKPMargin :
    YMBetaEstimateVerdict

  nonperturbativeBridgeRequired :
    YMBetaEstimateVerdict

data YMBalabanRGOpenStep : Set where
  constructNonperturbativeBlockSpinTransfer :
    YMBalabanRGOpenStep

  proveActualRhoDecreasesAcrossBalabanScale :
    YMBalabanRGOpenStep

  proveCarrierBetaPassesStrictMarginAfterRG :
    YMBalabanRGOpenStep

  connectCarrierScaleToContinuumOnlyAfterGate3 :
    YMBalabanRGOpenStep

canonicalYMBalabanRGOpenSteps :
  List YMBalabanRGOpenStep
canonicalYMBalabanRGOpenSteps =
  constructNonperturbativeBlockSpinTransfer
  ∷ proveActualRhoDecreasesAcrossBalabanScale
  ∷ proveCarrierBetaPassesStrictMarginAfterRG
  ∷ connectCarrierScaleToContinuumOnlyAfterGate3
  ∷ []

data YMBalabanRGNonClaim : Set where
  noPerturbativeThresholdPass :
    YMBalabanRGNonClaim

  noActualRhoRGDecreaseProof :
    YMBalabanRGNonClaim

  noBalabanConvergenceTheorem :
    YMBalabanRGNonClaim

  noContinuumYangMillsClaim :
    YMBalabanRGNonClaim

  noClayYangMillsPromotion :
    YMBalabanRGNonClaim

canonicalYMBalabanRGNonClaims :
  List YMBalabanRGNonClaim
canonicalYMBalabanRGNonClaims =
  noPerturbativeThresholdPass
  ∷ noActualRhoRGDecreaseProof
  ∷ noBalabanConvergenceTheorem
  ∷ noContinuumYangMillsClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMBalabanRGPromotion : Set where

ymBalabanRGPromotionImpossibleHere :
  YMBalabanRGPromotion →
  ⊥
ymBalabanRGPromotionImpossibleHere ()

oneLoopCarrierBetaNumerator :
  Nat
oneLoopCarrierBetaNumerator =
  769

oneLoopCarrierBetaDenominator :
  Nat
oneLoopCarrierBetaDenominator =
  100

twoLoopCarrierBetaNumerator :
  Nat
twoLoopCarrierBetaNumerator =
  800

twoLoopCarrierBetaDenominator :
  Nat
twoLoopCarrierBetaDenominator =
  100

strictKPMarginBetaNumerator :
  Nat
strictKPMarginBetaNumerator =
  1364

strictKPMarginBetaDenominator :
  Nat
strictKPMarginBetaDenominator =
  100

betaGapNumerator :
  Nat
betaGapNumerator =
  564

betaGapDenominator :
  Nat
betaGapDenominator =
  100

balabanRGSummary :
  String
balabanRGSummary =
  "YM6: one-loop beta ~=7.69 and two-loop beta ~=8.0 remain below the strict p=7 KP margin ~=13.64; the missing step is nonperturbative Balaban block-spin scale transfer for actual rho."

record YMBalabanRGScaleTransferFrontierReceipt : Setω where
  field
    status :
      YMBalabanRGScaleTransferStatus

    statusIsCanonical :
      status ≡ balabanRGScaleTransferFrontierRecorded

    consumedCouplingReceipt :
      KPC.KPCouplingObstructionReceipt

    couplingReceiptSaysRGRequired :
      KPC.kpRequiresRGFlow consumedCouplingReceipt
      ≡
      KPC.balabanRGFlowIsNecessaryInput

    consumedActualActivityReceipt :
      Actual.YMActualPolymerActivityDefinitionReceipt

    actualActivityStillMissing :
      Actual.actualPolymerActivitySupplied consumedActualActivityReceipt
      ≡
      false

    oneLoopVerdict :
      YMBetaEstimateVerdict

    oneLoopVerdictIsBelow :
      oneLoopVerdict ≡ oneLoopBelowStrictKPMargin

    twoLoopVerdict :
      YMBetaEstimateVerdict

    twoLoopVerdictIsBelow :
      twoLoopVerdict ≡ twoLoopBelowStrictKPMargin

    bridgeVerdict :
      YMBetaEstimateVerdict

    bridgeVerdictIsRequired :
      bridgeVerdict ≡ nonperturbativeBridgeRequired

    oneLoopBetaNumeratorRecorded :
      Nat

    oneLoopBetaNumeratorRecordedIsCanonical :
      oneLoopBetaNumeratorRecorded ≡ oneLoopCarrierBetaNumerator

    oneLoopBetaDenominatorRecorded :
      Nat

    oneLoopBetaDenominatorRecordedIsCanonical :
      oneLoopBetaDenominatorRecorded ≡ oneLoopCarrierBetaDenominator

    twoLoopBetaNumeratorRecorded :
      Nat

    twoLoopBetaNumeratorRecordedIsCanonical :
      twoLoopBetaNumeratorRecorded ≡ twoLoopCarrierBetaNumerator

    twoLoopBetaDenominatorRecorded :
      Nat

    twoLoopBetaDenominatorRecordedIsCanonical :
      twoLoopBetaDenominatorRecorded ≡ twoLoopCarrierBetaDenominator

    strictMarginBetaNumeratorRecorded :
      Nat

    strictMarginBetaNumeratorRecordedIsCanonical :
      strictMarginBetaNumeratorRecorded ≡ strictKPMarginBetaNumerator

    strictMarginBetaDenominatorRecorded :
      Nat

    strictMarginBetaDenominatorRecordedIsCanonical :
      strictMarginBetaDenominatorRecorded ≡ strictKPMarginBetaDenominator

    betaGapNumeratorRecorded :
      Nat

    betaGapNumeratorRecordedIsCanonical :
      betaGapNumeratorRecorded ≡ betaGapNumerator

    betaGapDenominatorRecorded :
      Nat

    betaGapDenominatorRecordedIsCanonical :
      betaGapDenominatorRecorded ≡ betaGapDenominator

    balabanRGProofPresent :
      Bool

    balabanRGProofPresentIsFalse :
      balabanRGProofPresent ≡ false

    openSteps :
      List YMBalabanRGOpenStep

    openStepsAreCanonical :
      openSteps ≡ canonicalYMBalabanRGOpenSteps

    nonClaims :
      List YMBalabanRGNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBalabanRGNonClaims

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ balabanRGSummary

open YMBalabanRGScaleTransferFrontierReceipt public

canonicalYMBalabanRGScaleTransferFrontierReceipt :
  YMBalabanRGScaleTransferFrontierReceipt
canonicalYMBalabanRGScaleTransferFrontierReceipt =
  record
    { status =
        balabanRGScaleTransferFrontierRecorded
    ; statusIsCanonical =
        refl
    ; consumedCouplingReceipt =
        KPC.canonicalKPCouplingObstructionReceipt
    ; couplingReceiptSaysRGRequired =
        refl
    ; consumedActualActivityReceipt =
        Actual.canonicalYMActualPolymerActivityDefinitionReceipt
    ; actualActivityStillMissing =
        refl
    ; oneLoopVerdict =
        oneLoopBelowStrictKPMargin
    ; oneLoopVerdictIsBelow =
        refl
    ; twoLoopVerdict =
        twoLoopBelowStrictKPMargin
    ; twoLoopVerdictIsBelow =
        refl
    ; bridgeVerdict =
        nonperturbativeBridgeRequired
    ; bridgeVerdictIsRequired =
        refl
    ; oneLoopBetaNumeratorRecorded =
        oneLoopCarrierBetaNumerator
    ; oneLoopBetaNumeratorRecordedIsCanonical =
        refl
    ; oneLoopBetaDenominatorRecorded =
        oneLoopCarrierBetaDenominator
    ; oneLoopBetaDenominatorRecordedIsCanonical =
        refl
    ; twoLoopBetaNumeratorRecorded =
        twoLoopCarrierBetaNumerator
    ; twoLoopBetaNumeratorRecordedIsCanonical =
        refl
    ; twoLoopBetaDenominatorRecorded =
        twoLoopCarrierBetaDenominator
    ; twoLoopBetaDenominatorRecordedIsCanonical =
        refl
    ; strictMarginBetaNumeratorRecorded =
        strictKPMarginBetaNumerator
    ; strictMarginBetaNumeratorRecordedIsCanonical =
        refl
    ; strictMarginBetaDenominatorRecorded =
        strictKPMarginBetaDenominator
    ; strictMarginBetaDenominatorRecordedIsCanonical =
        refl
    ; betaGapNumeratorRecorded =
        betaGapNumerator
    ; betaGapNumeratorRecordedIsCanonical =
        refl
    ; betaGapDenominatorRecorded =
        betaGapDenominator
    ; betaGapDenominatorRecordedIsCanonical =
        refl
    ; balabanRGProofPresent =
        false
    ; balabanRGProofPresentIsFalse =
        refl
    ; openSteps =
        canonicalYMBalabanRGOpenSteps
    ; openStepsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMBalabanRGNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; summary =
        balabanRGSummary
    ; summaryIsCanonical =
        refl
    }
