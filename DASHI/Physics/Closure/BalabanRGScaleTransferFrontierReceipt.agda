module DASHI.Physics.Closure.BalabanRGScaleTransferFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _<_; s≤s; z≤n)

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as Balaban

------------------------------------------------------------------------
-- Balaban RG scale-transfer frontier receipt.
--
-- This receipt records a perturbative scale-transfer diagnostic only:
-- one-loop and two-loop beta estimates are kept below the KP absorption
-- target with an explicit beta gap.  The nonperturbative Balaban
-- block-spin transfer, uniform KP absorption through the scale induction,
-- continuum Yang-Mills construction, and Clay promotion remain open.

data BalabanRGScaleTransferFrontierStatus : Set where
  perturbativeBetaBelowKPTarget_blockSpinTransferOpen :
    BalabanRGScaleTransferFrontierStatus

data BetaEstimateKind : Set where
  oneLoopPerturbativeEstimate :
    BetaEstimateKind

  twoLoopPerturbativeEstimate :
    BetaEstimateKind

  kpAbsorptionTarget :
    BetaEstimateKind

  betaGapToKPTarget :
    BetaEstimateKind

canonicalBetaEstimateKinds :
  List BetaEstimateKind
canonicalBetaEstimateKinds =
  oneLoopPerturbativeEstimate
  ∷ twoLoopPerturbativeEstimate
  ∷ kpAbsorptionTarget
  ∷ betaGapToKPTarget
  ∷ []

data BalabanScaleTransferFrontierComponent : Set where
  oneLoopBelowKPTargetComponent :
    BalabanScaleTransferFrontierComponent

  twoLoopBelowKPTargetComponent :
    BalabanScaleTransferFrontierComponent

  betaGapRecordedComponent :
    BalabanScaleTransferFrontierComponent

  uniformKPAbsorptionTargetComponent :
    BalabanScaleTransferFrontierComponent

  nonperturbativeBlockSpinTransferOpenComponent :
    BalabanScaleTransferFrontierComponent

canonicalBalabanScaleTransferFrontierComponents :
  List BalabanScaleTransferFrontierComponent
canonicalBalabanScaleTransferFrontierComponents =
  oneLoopBelowKPTargetComponent
  ∷ twoLoopBelowKPTargetComponent
  ∷ betaGapRecordedComponent
  ∷ uniformKPAbsorptionTargetComponent
  ∷ nonperturbativeBlockSpinTransferOpenComponent
  ∷ []

record NormalizedBetaEstimate : Set where
  field
    estimateKind :
      BetaEstimateKind

    numerator :
      Nat

    denominator :
      Nat

open NormalizedBetaEstimate public

betaScaleDenominator :
  Nat
betaScaleDenominator =
  100

oneLoopBetaNumerator :
  Nat
oneLoopBetaNumerator =
  1

twoLoopBetaNumerator :
  Nat
twoLoopBetaNumerator =
  2

kpAbsorptionTargetNumerator :
  Nat
kpAbsorptionTargetNumerator =
  3

betaGapNumerator :
  Nat
betaGapNumerator =
  1

oneLoopBetaEstimate :
  NormalizedBetaEstimate
oneLoopBetaEstimate =
  record
    { estimateKind =
        oneLoopPerturbativeEstimate
    ; numerator =
        oneLoopBetaNumerator
    ; denominator =
        betaScaleDenominator
    }

twoLoopBetaEstimate :
  NormalizedBetaEstimate
twoLoopBetaEstimate =
  record
    { estimateKind =
        twoLoopPerturbativeEstimate
    ; numerator =
        twoLoopBetaNumerator
    ; denominator =
        betaScaleDenominator
    }

kpAbsorptionTargetEstimate :
  NormalizedBetaEstimate
kpAbsorptionTargetEstimate =
  record
    { estimateKind =
        kpAbsorptionTarget
    ; numerator =
        kpAbsorptionTargetNumerator
    ; denominator =
        betaScaleDenominator
    }

betaGapEstimate :
  NormalizedBetaEstimate
betaGapEstimate =
  record
    { estimateKind =
        betaGapToKPTarget
    ; numerator =
        betaGapNumerator
    ; denominator =
        betaScaleDenominator
    }

data ScaleTransferOpenObligation : Set where
  proveUniformKoteckyPreissAbsorptionAcrossBlocks :
    ScaleTransferOpenObligation

  proveBalabanBlockSpinMapTransfersTheBetaMargin :
    ScaleTransferOpenObligation

  proveNonperturbativeLargeSmallFieldInduction :
    ScaleTransferOpenObligation

  proveContinuumScaleLimitFromBlockSpinTower :
    ScaleTransferOpenObligation

canonicalScaleTransferOpenObligations :
  List ScaleTransferOpenObligation
canonicalScaleTransferOpenObligations =
  proveUniformKoteckyPreissAbsorptionAcrossBlocks
  ∷ proveBalabanBlockSpinMapTransfersTheBetaMargin
  ∷ proveNonperturbativeLargeSmallFieldInduction
  ∷ proveContinuumScaleLimitFromBlockSpinTower
  ∷ []

data BalabanRGScaleTransferPromotion : Set where

balabanRGScaleTransferPromotionImpossibleHere :
  BalabanRGScaleTransferPromotion →
  ⊥
balabanRGScaleTransferPromotionImpossibleHere ()

oneLoopBelowKPTarget :
  oneLoopBetaNumerator < kpAbsorptionTargetNumerator
oneLoopBelowKPTarget =
  s≤s (s≤s z≤n)

twoLoopBelowKPTarget :
  twoLoopBetaNumerator < kpAbsorptionTargetNumerator
twoLoopBelowKPTarget =
  s≤s (s≤s (s≤s z≤n))

betaGapClosesTwoLoopToKPTarget :
  twoLoopBetaNumerator + betaGapNumerator
  ≡
  kpAbsorptionTargetNumerator
betaGapClosesTwoLoopToKPTarget =
  refl

betaEstimateBoundaryStatement :
  String
betaEstimateBoundaryStatement =
  "Normalized perturbative beta estimates are recorded as one-loop 1/100 and two-loop 2/100 below the KP absorption target 3/100; the beta gap from two-loop to target is 1/100."

balabanBlockSpinBoundaryStatement :
  String
balabanBlockSpinBoundaryStatement =
  "The perturbative beta gap is diagnostic only: nonperturbative Balaban block-spin scale transfer and uniform KP absorption through the induction remain open."

record BalabanRGScaleTransferFrontierReceipt : Setω where
  field
    status :
      BalabanRGScaleTransferFrontierStatus

    statusIsFrontier :
      status
      ≡
      perturbativeBetaBelowKPTarget_blockSpinTransferOpen

    balabanMassGapSurface :
      Balaban.BalabanRGMassGapReceiptSurface

    balabanContinuumMassGapStillFalse :
      Balaban.continuumMassGapProvedInDASHI balabanMassGapSurface
      ≡
      false

    balabanClayPromotionStillFalse :
      Balaban.continuumClayMassGapPromoted balabanMassGapSurface
      ≡
      false

    estimateKinds :
      List BetaEstimateKind

    estimateKindsAreCanonical :
      estimateKinds ≡ canonicalBetaEstimateKinds

    oneLoopEstimate :
      NormalizedBetaEstimate

    oneLoopEstimateIsCanonical :
      oneLoopEstimate ≡ oneLoopBetaEstimate

    twoLoopEstimate :
      NormalizedBetaEstimate

    twoLoopEstimateIsCanonical :
      twoLoopEstimate ≡ twoLoopBetaEstimate

    kpTargetEstimate :
      NormalizedBetaEstimate

    kpTargetEstimateIsCanonical :
      kpTargetEstimate ≡ kpAbsorptionTargetEstimate

    betaGapEstimateRecord :
      NormalizedBetaEstimate

    betaGapEstimateRecordIsCanonical :
      betaGapEstimateRecord ≡ betaGapEstimate

    commonDenominator :
      Nat

    commonDenominatorIsCanonical :
      commonDenominator ≡ betaScaleDenominator

    oneLoopNumeratorBelowKPTarget :
      oneLoopBetaNumerator < kpAbsorptionTargetNumerator

    oneLoopNumeratorBelowKPTargetIsCanonical :
      oneLoopNumeratorBelowKPTarget ≡ oneLoopBelowKPTarget

    twoLoopNumeratorBelowKPTarget :
      twoLoopBetaNumerator < kpAbsorptionTargetNumerator

    twoLoopNumeratorBelowKPTargetIsCanonical :
      twoLoopNumeratorBelowKPTarget ≡ twoLoopBelowKPTarget

    betaGapNumeratorRecord :
      Nat

    betaGapNumeratorRecordIsCanonical :
      betaGapNumeratorRecord ≡ betaGapNumerator

    betaGapClosesTwoLoopToTarget :
      twoLoopBetaNumerator + betaGapNumerator
      ≡
      kpAbsorptionTargetNumerator

    betaGapClosesTwoLoopToTargetIsCanonical :
      betaGapClosesTwoLoopToTarget
      ≡
      betaGapClosesTwoLoopToKPTarget

    frontierComponents :
      List BalabanScaleTransferFrontierComponent

    frontierComponentsAreCanonical :
      frontierComponents
      ≡
      canonicalBalabanScaleTransferFrontierComponents

    openObligations :
      List ScaleTransferOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalScaleTransferOpenObligations

    kpAbsorptionTargetRecorded :
      Bool

    kpAbsorptionTargetRecordedIsTrue :
      kpAbsorptionTargetRecorded ≡ true

    perturbativeEstimatesBelowTarget :
      Bool

    perturbativeEstimatesBelowTargetIsTrue :
      perturbativeEstimatesBelowTarget ≡ true

    betaGapRecorded :
      Bool

    betaGapRecordedIsTrue :
      betaGapRecorded ≡ true

    perturbativeEstimatePromotedToNonperturbativeTransfer :
      Bool

    perturbativeEstimatePromotedToNonperturbativeTransferIsFalse :
      perturbativeEstimatePromotedToNonperturbativeTransfer ≡ false

    balabanBlockSpinTransferProved :
      Bool

    balabanBlockSpinTransferProvedIsFalse :
      balabanBlockSpinTransferProved ≡ false

    uniformKPAbsorptionThroughBalabanInductionProved :
      Bool

    uniformKPAbsorptionThroughBalabanInductionProvedIsFalse :
      uniformKPAbsorptionThroughBalabanInductionProved ≡ false

    continuumYangMillsConstructedHere :
      Bool

    continuumYangMillsConstructedHereIsFalse :
      continuumYangMillsConstructedHere ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotionFlags :
      List BalabanRGScaleTransferPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    betaEstimateBoundary :
      String

    betaEstimateBoundaryIsCanonical :
      betaEstimateBoundary ≡ betaEstimateBoundaryStatement

    blockSpinBoundary :
      String

    blockSpinBoundaryIsCanonical :
      blockSpinBoundary ≡ balabanBlockSpinBoundaryStatement

open BalabanRGScaleTransferFrontierReceipt public

canonicalBalabanRGScaleTransferFrontierReceipt :
  BalabanRGScaleTransferFrontierReceipt
canonicalBalabanRGScaleTransferFrontierReceipt =
  record
    { status =
        perturbativeBetaBelowKPTarget_blockSpinTransferOpen
    ; statusIsFrontier =
        refl
    ; balabanMassGapSurface =
        Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; balabanContinuumMassGapStillFalse =
        refl
    ; balabanClayPromotionStillFalse =
        refl
    ; estimateKinds =
        canonicalBetaEstimateKinds
    ; estimateKindsAreCanonical =
        refl
    ; oneLoopEstimate =
        oneLoopBetaEstimate
    ; oneLoopEstimateIsCanonical =
        refl
    ; twoLoopEstimate =
        twoLoopBetaEstimate
    ; twoLoopEstimateIsCanonical =
        refl
    ; kpTargetEstimate =
        kpAbsorptionTargetEstimate
    ; kpTargetEstimateIsCanonical =
        refl
    ; betaGapEstimateRecord =
        betaGapEstimate
    ; betaGapEstimateRecordIsCanonical =
        refl
    ; commonDenominator =
        betaScaleDenominator
    ; commonDenominatorIsCanonical =
        refl
    ; oneLoopNumeratorBelowKPTarget =
        oneLoopBelowKPTarget
    ; oneLoopNumeratorBelowKPTargetIsCanonical =
        refl
    ; twoLoopNumeratorBelowKPTarget =
        twoLoopBelowKPTarget
    ; twoLoopNumeratorBelowKPTargetIsCanonical =
        refl
    ; betaGapNumeratorRecord =
        betaGapNumerator
    ; betaGapNumeratorRecordIsCanonical =
        refl
    ; betaGapClosesTwoLoopToTarget =
        betaGapClosesTwoLoopToKPTarget
    ; betaGapClosesTwoLoopToTargetIsCanonical =
        refl
    ; frontierComponents =
        canonicalBalabanScaleTransferFrontierComponents
    ; frontierComponentsAreCanonical =
        refl
    ; openObligations =
        canonicalScaleTransferOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; kpAbsorptionTargetRecorded =
        true
    ; kpAbsorptionTargetRecordedIsTrue =
        refl
    ; perturbativeEstimatesBelowTarget =
        true
    ; perturbativeEstimatesBelowTargetIsTrue =
        refl
    ; betaGapRecorded =
        true
    ; betaGapRecordedIsTrue =
        refl
    ; perturbativeEstimatePromotedToNonperturbativeTransfer =
        false
    ; perturbativeEstimatePromotedToNonperturbativeTransferIsFalse =
        refl
    ; balabanBlockSpinTransferProved =
        false
    ; balabanBlockSpinTransferProvedIsFalse =
        refl
    ; uniformKPAbsorptionThroughBalabanInductionProved =
        false
    ; uniformKPAbsorptionThroughBalabanInductionProvedIsFalse =
        refl
    ; continuumYangMillsConstructedHere =
        false
    ; continuumYangMillsConstructedHereIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; betaEstimateBoundary =
        betaEstimateBoundaryStatement
    ; betaEstimateBoundaryIsCanonical =
        refl
    ; blockSpinBoundary =
        balabanBlockSpinBoundaryStatement
    ; blockSpinBoundaryIsCanonical =
        refl
    }

canonicalBalabanRGScaleTransferRecordsBetaGap :
  betaGapClosesTwoLoopToTarget
    canonicalBalabanRGScaleTransferFrontierReceipt
  ≡
  betaGapClosesTwoLoopToKPTarget
canonicalBalabanRGScaleTransferRecordsBetaGap =
  refl

canonicalBalabanRGScaleTransferBlockSpinStillOpen :
  balabanBlockSpinTransferProved
    canonicalBalabanRGScaleTransferFrontierReceipt
  ≡
  false
canonicalBalabanRGScaleTransferBlockSpinStillOpen =
  refl

canonicalBalabanRGScaleTransferNoClayPromotion :
  clayYangMillsPromoted canonicalBalabanRGScaleTransferFrontierReceipt
  ≡
  false
canonicalBalabanRGScaleTransferNoClayPromotion =
  refl
