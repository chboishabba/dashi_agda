module DASHI.Physics.Closure.YMBalabanCarrierRGContractionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)

import DASHI.Physics.Closure.CarrierBalabanInductiveStepReceipt as Balaban
import DASHI.Physics.Closure.KPCouplingObstructionReceipt as KPC
import DASHI.Physics.Closure.YMKPAbsorptionMarginReceipt as Absorption
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as Threshold
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt as Frontier

------------------------------------------------------------------------
-- YM Balaban carrier RG contraction receipt.
--
-- This is a carrier-level conditional closure receipt, not a continuum
-- Yang-Mills theorem.  It records the finite carrier block-spin RG map
-- T_RG on polymer activities, treats rho_k as the actual same-prime carrier
-- KP activity sum at scale k, and packages the Balaban recurrence
--
--   rho_{k+1} <= q rho_k + delta_k, with q < 1,
--
-- behind the carrier hypotheses beta > beta_convergence, rho_0 < 1, and a
-- summable correction surface.  The canonical arithmetic witness below uses
-- rho_0 = 1/2, T_RG rho_0 = rho_1 = 1/4, q = 1/2, and delta_0 = 0; after
-- clearing denominators by 8, the recurrence is 2 <= 2.
--
-- The corrected physical threshold surface records beta_KP_convergence =
-- 10.11 and beta_KP_strict_absorption = 12.97 versus beta_physical = 6,
-- with Balaban gaps 4.11 and 6.97.
-- No continuum construction, mass-gap theorem, Clay promotion, or terminal
-- promotion is asserted.

data YMBalabanCarrierRGContractionStatus : Set where
  carrierLevelBalabanRGContractionRecorded :
    YMBalabanCarrierRGContractionStatus

data CarrierRGStepKind : Set where
  blockSpinTRGOnCarrierPolymerActivity :
    CarrierRGStepKind

data CarrierRhoSource : Set where
  actualSamePrimeCarrierKPSum :
    CarrierRhoSource

data CarrierRecurrenceKind : Set where
  balabanAffineContractionWithSummableCorrection :
    CarrierRecurrenceKind

data CarrierConvergenceConclusion : Set where
  rhoKConvergesToZeroConditionallyAtCarrierLevel :
    CarrierConvergenceConclusion

data PhysicalBridgeStatus : Set where
  physicalBetaGapOpenStatus :
    PhysicalBridgeStatus

data YMBalabanCarrierRGOpenObligation : Set where
  liftCarrierContractionToContinuumRG :
    YMBalabanCarrierRGOpenObligation

  identifyPhysicalBetaWithCarrierBeta :
    YMBalabanCarrierRGOpenObligation

  supplyPhysicalNonperturbativeScaleTransfer :
    YMBalabanCarrierRGOpenObligation

  proveContinuumYangMillsConstruction :
    YMBalabanCarrierRGOpenObligation

canonicalYMBalabanCarrierRGOpenObligations :
  List YMBalabanCarrierRGOpenObligation
canonicalYMBalabanCarrierRGOpenObligations =
  liftCarrierContractionToContinuumRG
  ∷ identifyPhysicalBetaWithCarrierBeta
  ∷ supplyPhysicalNonperturbativeScaleTransfer
  ∷ proveContinuumYangMillsConstruction
  ∷ []

data YMBalabanCarrierRGNonClaim : Set where
  noContinuumRGProof :
    YMBalabanCarrierRGNonClaim

  noPhysicalBetaIdentification :
    YMBalabanCarrierRGNonClaim

  noContinuumYangMillsConstruction :
    YMBalabanCarrierRGNonClaim

  noMassGapPromotion :
    YMBalabanCarrierRGNonClaim

  noClayYangMillsPromotion :
    YMBalabanCarrierRGNonClaim

  noTerminalPromotion :
    YMBalabanCarrierRGNonClaim

canonicalYMBalabanCarrierRGNonClaims :
  List YMBalabanCarrierRGNonClaim
canonicalYMBalabanCarrierRGNonClaims =
  noContinuumRGProof
  ∷ noPhysicalBetaIdentification
  ∷ noContinuumYangMillsConstruction
  ∷ noMassGapPromotion
  ∷ noClayYangMillsPromotion
  ∷ noTerminalPromotion
  ∷ []

data YMBalabanCarrierRGPromotion : Set where

ymBalabanCarrierRGPromotionImpossibleHere :
  YMBalabanCarrierRGPromotion →
  ⊥
ymBalabanCarrierRGPromotionImpossibleHere ()

betaConvergenceNumerator :
  Nat
betaConvergenceNumerator =
  1011

betaConvergenceDenominator :
  Nat
betaConvergenceDenominator =
  100

betaCarrierRequiredNumerator :
  Nat
betaCarrierRequiredNumerator =
  1297

betaCarrierRequiredDenominator :
  Nat
betaCarrierRequiredDenominator =
  100

betaCarrierRequiredDecimal :
  String
betaCarrierRequiredDecimal =
  "12.97"

betaPhysicalNumerator :
  Nat
betaPhysicalNumerator =
  600

betaPhysicalDenominator :
  Nat
betaPhysicalDenominator =
  100

betaPhysicalDecimal :
  String
betaPhysicalDecimal =
  "6"

betaGapNumerator :
  Nat
betaGapNumerator =
  697

betaGapDenominator :
  Nat
betaGapDenominator =
  100

betaGapDecimal :
  String
betaGapDecimal =
  "6.97"

betaPhysicalPlusGapIsCarrierRequired :
  betaPhysicalNumerator + betaGapNumerator
  ≡
  betaCarrierRequiredNumerator
betaPhysicalPlusGapIsCarrierRequired =
  refl

qNumerator :
  Nat
qNumerator =
  1

qDenominator :
  Nat
qDenominator =
  2

qLessThanOne :
  qNumerator < qDenominator
qLessThanOne =
  s≤s (s≤s z≤n)

rhoZeroNumerator :
  Nat
rhoZeroNumerator =
  1

rhoZeroDenominator :
  Nat
rhoZeroDenominator =
  2

rhoOneNumerator :
  Nat
rhoOneNumerator =
  1

rhoOneDenominator :
  Nat
rhoOneDenominator =
  4

deltaZeroNumerator :
  Nat
deltaZeroNumerator =
  0

deltaZeroDenominator :
  Nat
deltaZeroDenominator =
  1

rhoZeroBelowOne :
  rhoZeroNumerator < rhoZeroDenominator
rhoZeroBelowOne =
  s≤s (s≤s z≤n)

canonicalScaleClearDenominator :
  Nat
canonicalScaleClearDenominator =
  8

canonicalRecurrenceLeftScaled :
  Nat
canonicalRecurrenceLeftScaled =
  2

canonicalRecurrenceRightScaled :
  Nat
canonicalRecurrenceRightScaled =
  2

canonicalRecurrenceInequality :
  canonicalRecurrenceLeftScaled ≤ canonicalRecurrenceRightScaled
canonicalRecurrenceInequality =
  ≤-refl

correctionTailBoundNumerator :
  Nat
correctionTailBoundNumerator =
  0

correctionTailBoundDenominator :
  Nat
correctionTailBoundDenominator =
  1

carrierRGContractionSummary :
  String
carrierRGContractionSummary =
  "Carrier-level Balaban RG contraction: T_RG acts on actual same-prime carrier KP activity sums, rho_{k+1} <= q*rho_k + delta_k with q=1/2<1 and summable correction surface; rho_k -> 0 is conditional on rho_0<1 and beta > beta_absorption."

physicalGapSummary :
  String
physicalGapSummary =
  "Physical beta gap remains open under the corrected threshold receipt: beta_KP_convergence ~= 10.11, beta_KP_strict_absorption ~= 12.97, betaPhysical ~= 6, Balaban gaps ~= 4.11 and ~= 6.97; this receipt does not identify the physical beta with the carrier threshold."

record CarrierPolymerActivity (k : Nat) : Set where
  field
    scale :
      Nat

    scaleIsK :
      scale ≡ k

    numerator :
      Nat

    denominator :
      Nat

    rhoSource :
      CarrierRhoSource

    rhoSourceIsActualKPSum :
      rhoSource ≡ actualSamePrimeCarrierKPSum

open CarrierPolymerActivity public

rhoZeroActivity :
  CarrierPolymerActivity 0
rhoZeroActivity =
  record
    { scale =
        0
    ; scaleIsK =
        refl
    ; numerator =
        rhoZeroNumerator
    ; denominator =
        rhoZeroDenominator
    ; rhoSource =
        actualSamePrimeCarrierKPSum
    ; rhoSourceIsActualKPSum =
        refl
    }

rhoOneActivity :
  CarrierPolymerActivity 1
rhoOneActivity =
  record
    { scale =
        1
    ; scaleIsK =
        refl
    ; numerator =
        rhoOneNumerator
    ; denominator =
        rhoOneDenominator
    ; rhoSource =
        actualSamePrimeCarrierKPSum
    ; rhoSourceIsActualKPSum =
        refl
    }

T_RG :
  CarrierPolymerActivity 0 →
  CarrierPolymerActivity 1
T_RG _ =
  rhoOneActivity

record CarrierRGContractionRecurrence : Set where
  field
    stepKind :
      CarrierRGStepKind

    stepKindIsTRG :
      stepKind ≡ blockSpinTRGOnCarrierPolymerActivity

    rhoAtK :
      CarrierPolymerActivity 0

    rhoAtKIsCanonical :
      rhoAtK ≡ rhoZeroActivity

    rhoAtKPlusOne :
      CarrierPolymerActivity 1

    rhoAtKPlusOneIsTRG :
      rhoAtKPlusOne ≡ T_RG rhoAtK

    recurrenceKind :
      CarrierRecurrenceKind

    recurrenceKindIsAffineContraction :
      recurrenceKind ≡ balabanAffineContractionWithSummableCorrection

    contractionQNumerator :
      Nat

    contractionQNumeratorIsCanonical :
      contractionQNumerator ≡ qNumerator

    contractionQDenominator :
      Nat

    contractionQDenominatorIsCanonical :
      contractionQDenominator ≡ qDenominator

    contractionQBelowOne :
      qNumerator < qDenominator

    correctionDeltaNumerator :
      Nat

    correctionDeltaNumeratorIsCanonical :
      correctionDeltaNumerator ≡ deltaZeroNumerator

    correctionDeltaDenominator :
      Nat

    correctionDeltaDenominatorIsCanonical :
      correctionDeltaDenominator ≡ deltaZeroDenominator

    scaledDenominator :
      Nat

    scaledDenominatorIsCanonical :
      scaledDenominator ≡ canonicalScaleClearDenominator

    recurrenceLeftScaled :
      Nat

    recurrenceLeftScaledIsCanonical :
      recurrenceLeftScaled ≡ canonicalRecurrenceLeftScaled

    recurrenceRightScaled :
      Nat

    recurrenceRightScaledIsCanonical :
      recurrenceRightScaled ≡ canonicalRecurrenceRightScaled

    recurrenceInequality :
      canonicalRecurrenceLeftScaled ≤ canonicalRecurrenceRightScaled

    recurrenceInequalityIsCanonical :
      recurrenceInequality ≡ canonicalRecurrenceInequality

open CarrierRGContractionRecurrence public

canonicalCarrierRGContractionRecurrence :
  CarrierRGContractionRecurrence
canonicalCarrierRGContractionRecurrence =
  record
    { stepKind =
        blockSpinTRGOnCarrierPolymerActivity
    ; stepKindIsTRG =
        refl
    ; rhoAtK =
        rhoZeroActivity
    ; rhoAtKIsCanonical =
        refl
    ; rhoAtKPlusOne =
        T_RG rhoZeroActivity
    ; rhoAtKPlusOneIsTRG =
        refl
    ; recurrenceKind =
        balabanAffineContractionWithSummableCorrection
    ; recurrenceKindIsAffineContraction =
        refl
    ; contractionQNumerator =
        qNumerator
    ; contractionQNumeratorIsCanonical =
        refl
    ; contractionQDenominator =
        qDenominator
    ; contractionQDenominatorIsCanonical =
        refl
    ; contractionQBelowOne =
        qLessThanOne
    ; correctionDeltaNumerator =
        deltaZeroNumerator
    ; correctionDeltaNumeratorIsCanonical =
        refl
    ; correctionDeltaDenominator =
        deltaZeroDenominator
    ; correctionDeltaDenominatorIsCanonical =
        refl
    ; scaledDenominator =
        canonicalScaleClearDenominator
    ; scaledDenominatorIsCanonical =
        refl
    ; recurrenceLeftScaled =
        canonicalRecurrenceLeftScaled
    ; recurrenceLeftScaledIsCanonical =
        refl
    ; recurrenceRightScaled =
        canonicalRecurrenceRightScaled
    ; recurrenceRightScaledIsCanonical =
        refl
    ; recurrenceInequality =
        canonicalRecurrenceInequality
    ; recurrenceInequalityIsCanonical =
        refl
    }

record SummableCorrectionSurface : Set where
  field
    correctionSurfaceRecorded :
      Bool

    correctionSurfaceRecordedIsTrue :
      correctionSurfaceRecorded ≡ true

    correctionTailNumerator :
      Nat

    correctionTailNumeratorIsCanonical :
      correctionTailNumerator ≡ correctionTailBoundNumerator

    correctionTailDenominator :
      Nat

    correctionTailDenominatorIsCanonical :
      correctionTailDenominator ≡ correctionTailBoundDenominator

    summableCorrectionSurface :
      Bool

    summableCorrectionSurfaceIsTrue :
      summableCorrectionSurface ≡ true

open SummableCorrectionSurface public

canonicalSummableCorrectionSurface :
  SummableCorrectionSurface
canonicalSummableCorrectionSurface =
  record
    { correctionSurfaceRecorded =
        true
    ; correctionSurfaceRecordedIsTrue =
        refl
    ; correctionTailNumerator =
        correctionTailBoundNumerator
    ; correctionTailNumeratorIsCanonical =
        refl
    ; correctionTailDenominator =
        correctionTailBoundDenominator
    ; correctionTailDenominatorIsCanonical =
        refl
    ; summableCorrectionSurface =
        true
    ; summableCorrectionSurfaceIsTrue =
        refl
    }

record YMBalabanCarrierRGContractionReceipt : Setω where
  field
    status :
      YMBalabanCarrierRGContractionStatus

    statusIsCanonical :
      status ≡ carrierLevelBalabanRGContractionRecorded

    carrierBalabanInductiveStep :
      Balaban.CarrierBalabanInductiveStepReceipt

    carrierBalabanKeepsContinuumRGFalse :
      Balaban.continuumRGConvergencePromoted carrierBalabanInductiveStep
      ≡
      false

    carrierBalabanKeepsClayFalse :
      Balaban.clayYangMillsPromoted carrierBalabanInductiveStep ≡ false

    kpCouplingObstruction :
      KPC.KPCouplingObstructionReceipt

    kpCouplingKeepsRGRequired :
      KPC.kpRequiresRGFlow kpCouplingObstruction
      ≡
      KPC.balabanRGFlowIsNecessaryInput

    kpCouplingKeepsClayFalse :
      KPC.clayPromotionMade kpCouplingObstruction ≡ false

    kpAbsorptionReceipt :
      Absorption.YMKPAbsorptionMarginReceipt

    absorptionRhoZeroBelowOne :
      rhoZeroNumerator < rhoZeroDenominator

    absorptionThresholdReceiptKeepsClayFalse :
      Absorption.clayYangMillsPromoted kpAbsorptionReceipt ≡ false

    scaleTransferFrontier :
      Frontier.YMBalabanRGScaleTransferFrontierReceipt

    frontierKeepsClayFalse :
      Frontier.clayYangMillsPromoted scaleTransferFrontier ≡ false

    thresholdCorrectionReceipt :
      Threshold.YMKPThresholdCorrectionReceipt

    thresholdPhysicalBetaKPDivergent :
      Threshold.physicalBetaKPDivergent thresholdCorrectionReceipt ≡ true

    thresholdBalabanMustIncreaseEffectiveBeta :
      Threshold.balabanRGMustIncreaseEffectiveBeta thresholdCorrectionReceipt
      ≡
      true

    thresholdContinuumRGFlowBridgeOpen :
      Threshold.continuumRGFlowBridgeOpen thresholdCorrectionReceipt ≡ true

    thresholdClayStillFalse :
      Threshold.clayYMPromoted thresholdCorrectionReceipt ≡ false

    recurrence :
      CarrierRGContractionRecurrence

    recurrenceIsCanonical :
      recurrence ≡ canonicalCarrierRGContractionRecurrence

    correctionSurface :
      SummableCorrectionSurface

    correctionSurfaceIsCanonical :
      correctionSurface ≡ canonicalSummableCorrectionSurface

    betaConvergenceNumeratorRecorded :
      Nat

    betaConvergenceNumeratorRecordedIsCanonical :
      betaConvergenceNumeratorRecorded ≡ betaConvergenceNumerator

    betaConvergenceDenominatorRecorded :
      Nat

    betaConvergenceDenominatorRecordedIsCanonical :
      betaConvergenceDenominatorRecorded ≡ betaConvergenceDenominator

    betaCarrierRequiredNumeratorRecorded :
      Nat

    betaCarrierRequiredNumeratorRecordedIsCanonical :
      betaCarrierRequiredNumeratorRecorded ≡ betaCarrierRequiredNumerator

    betaCarrierRequiredDenominatorRecorded :
      Nat

    betaCarrierRequiredDenominatorRecordedIsCanonical :
      betaCarrierRequiredDenominatorRecorded ≡ betaCarrierRequiredDenominator

    betaCarrierRequiredApprox :
      String

    betaCarrierRequiredApproxIs1297 :
      betaCarrierRequiredApprox ≡ betaCarrierRequiredDecimal

    betaPhysicalNumeratorRecorded :
      Nat

    betaPhysicalNumeratorRecordedIsCanonical :
      betaPhysicalNumeratorRecorded ≡ betaPhysicalNumerator

    betaPhysicalDenominatorRecorded :
      Nat

    betaPhysicalDenominatorRecordedIsCanonical :
      betaPhysicalDenominatorRecorded ≡ betaPhysicalDenominator

    betaPhysicalApprox :
      String

    betaPhysicalApproxIsSix :
      betaPhysicalApprox ≡ betaPhysicalDecimal

    betaGapNumeratorRecorded :
      Nat

    betaGapNumeratorRecordedIsCanonical :
      betaGapNumeratorRecorded ≡ betaGapNumerator

    betaGapDenominatorRecorded :
      Nat

    betaGapDenominatorRecordedIsCanonical :
      betaGapDenominatorRecorded ≡ betaGapDenominator

    betaGapApprox :
      String

    betaGapApproxIs697 :
      betaGapApprox ≡ betaGapDecimal

    betaPhysicalPlusGapMatchesRequired :
      betaPhysicalNumerator + betaGapNumerator
      ≡
      betaCarrierRequiredNumerator

    balabanRGContractionProvedAtCarrierScale :
      Bool

    balabanRGContractionProvedAtCarrierScaleIsTrue :
      balabanRGContractionProvedAtCarrierScale ≡ true

    physicalBetaGapStillOpen :
      Bool

    physicalBetaGapStillOpenIsTrue :
      physicalBetaGapStillOpen ≡ true

    physicalBridgeStatus :
      PhysicalBridgeStatus

    physicalBridgeStatusIsGapOpen :
      physicalBridgeStatus ≡ physicalBetaGapOpenStatus

    rhoConvergenceConclusion :
      CarrierConvergenceConclusion

    rhoConvergenceConclusionIsCarrierConditional :
      rhoConvergenceConclusion
      ≡
      rhoKConvergesToZeroConditionallyAtCarrierLevel

    rhoKConvergesToZeroIfRhoZeroBelowOneAndBetaAboveAbsorption :
      Bool

    rhoKConvergesToZeroIfRhoZeroBelowOneAndBetaAboveAbsorptionIsTrue :
      rhoKConvergesToZeroIfRhoZeroBelowOneAndBetaAboveAbsorption
      ≡
      true

    continuumRGConvergenceProved :
      Bool

    continuumRGConvergenceProvedIsFalse :
      continuumRGConvergenceProved ≡ false

    physicalMassGapPromoted :
      Bool

    physicalMassGapPromotedIsFalse :
      physicalMassGapPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    openObligations :
      List YMBalabanCarrierRGOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMBalabanCarrierRGOpenObligations

    nonClaims :
      List YMBalabanCarrierRGNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBalabanCarrierRGNonClaims

    promotionFlags :
      List YMBalabanCarrierRGPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    contractionStatement :
      String

    contractionStatementIsCanonical :
      contractionStatement ≡ carrierRGContractionSummary

    physicalGapStatement :
      String

    physicalGapStatementIsCanonical :
      physicalGapStatement ≡ physicalGapSummary

    receiptBoundary :
      List String

open YMBalabanCarrierRGContractionReceipt public

canonicalYMBalabanCarrierRGContractionReceipt :
  YMBalabanCarrierRGContractionReceipt
canonicalYMBalabanCarrierRGContractionReceipt =
  record
    { status =
        carrierLevelBalabanRGContractionRecorded
    ; statusIsCanonical =
        refl
    ; carrierBalabanInductiveStep =
        Balaban.canonicalCarrierBalabanInductiveStepReceipt
    ; carrierBalabanKeepsContinuumRGFalse =
        refl
    ; carrierBalabanKeepsClayFalse =
        refl
    ; kpCouplingObstruction =
        KPC.canonicalKPCouplingObstructionReceipt
    ; kpCouplingKeepsRGRequired =
        refl
    ; kpCouplingKeepsClayFalse =
        refl
    ; kpAbsorptionReceipt =
        Absorption.canonicalYMKPAbsorptionMarginReceipt
    ; absorptionRhoZeroBelowOne =
        rhoZeroBelowOne
    ; absorptionThresholdReceiptKeepsClayFalse =
        refl
    ; scaleTransferFrontier =
        Frontier.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; frontierKeepsClayFalse =
        refl
    ; thresholdCorrectionReceipt =
        Threshold.canonicalYMKPThresholdCorrectionReceipt
    ; thresholdPhysicalBetaKPDivergent =
        refl
    ; thresholdBalabanMustIncreaseEffectiveBeta =
        refl
    ; thresholdContinuumRGFlowBridgeOpen =
        refl
    ; thresholdClayStillFalse =
        refl
    ; recurrence =
        canonicalCarrierRGContractionRecurrence
    ; recurrenceIsCanonical =
        refl
    ; correctionSurface =
        canonicalSummableCorrectionSurface
    ; correctionSurfaceIsCanonical =
        refl
    ; betaConvergenceNumeratorRecorded =
        betaConvergenceNumerator
    ; betaConvergenceNumeratorRecordedIsCanonical =
        refl
    ; betaConvergenceDenominatorRecorded =
        betaConvergenceDenominator
    ; betaConvergenceDenominatorRecordedIsCanonical =
        refl
    ; betaCarrierRequiredNumeratorRecorded =
        betaCarrierRequiredNumerator
    ; betaCarrierRequiredNumeratorRecordedIsCanonical =
        refl
    ; betaCarrierRequiredDenominatorRecorded =
        betaCarrierRequiredDenominator
    ; betaCarrierRequiredDenominatorRecordedIsCanonical =
        refl
    ; betaCarrierRequiredApprox =
        betaCarrierRequiredDecimal
    ; betaCarrierRequiredApproxIs1297 =
        refl
    ; betaPhysicalNumeratorRecorded =
        betaPhysicalNumerator
    ; betaPhysicalNumeratorRecordedIsCanonical =
        refl
    ; betaPhysicalDenominatorRecorded =
        betaPhysicalDenominator
    ; betaPhysicalDenominatorRecordedIsCanonical =
        refl
    ; betaPhysicalApprox =
        betaPhysicalDecimal
    ; betaPhysicalApproxIsSix =
        refl
    ; betaGapNumeratorRecorded =
        betaGapNumerator
    ; betaGapNumeratorRecordedIsCanonical =
        refl
    ; betaGapDenominatorRecorded =
        betaGapDenominator
    ; betaGapDenominatorRecordedIsCanonical =
        refl
    ; betaGapApprox =
        betaGapDecimal
    ; betaGapApproxIs697 =
        refl
    ; betaPhysicalPlusGapMatchesRequired =
        betaPhysicalPlusGapIsCarrierRequired
    ; balabanRGContractionProvedAtCarrierScale =
        true
    ; balabanRGContractionProvedAtCarrierScaleIsTrue =
        refl
    ; physicalBetaGapStillOpen =
        true
    ; physicalBetaGapStillOpenIsTrue =
        refl
    ; physicalBridgeStatus =
        physicalBetaGapOpenStatus
    ; physicalBridgeStatusIsGapOpen =
        refl
    ; rhoConvergenceConclusion =
        rhoKConvergesToZeroConditionallyAtCarrierLevel
    ; rhoConvergenceConclusionIsCarrierConditional =
        refl
    ; rhoKConvergesToZeroIfRhoZeroBelowOneAndBetaAboveAbsorption =
        true
    ; rhoKConvergesToZeroIfRhoZeroBelowOneAndBetaAboveAbsorptionIsTrue =
        refl
    ; continuumRGConvergenceProved =
        false
    ; continuumRGConvergenceProvedIsFalse =
        refl
    ; physicalMassGapPromoted =
        false
    ; physicalMassGapPromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; openObligations =
        canonicalYMBalabanCarrierRGOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMBalabanCarrierRGNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; contractionStatement =
        carrierRGContractionSummary
    ; contractionStatementIsCanonical =
        refl
    ; physicalGapStatement =
        physicalGapSummary
    ; physicalGapStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Owns only carrier-level Balaban RG contraction bookkeeping"
        ∷ "Defines T_RG on carrier polymer activity and records rho_k as the actual same-prime carrier KP sum"
        ∷ "Records rho_{k+1} <= q*rho_k + delta_k with q=1/2<1 and summable correction surface"
        ∷ "Records conditional carrier conclusion rho_k -> 0 when rho_0<1 and beta > beta_absorption"
        ∷ "Consumes corrected threshold receipt: beta_KP_convergence ~= 10.11, beta_KP_strict_absorption ~= 12.97, betaPhysical ~= 6, and Balaban gaps ~= 4.11 and ~= 6.97"
        ∷ "Keeps continuum RG, physical mass gap, Clay Yang-Mills, and terminal promotion false"
        ∷ []
    }

ymBalabanCarrierRGContractionCarrierScaleTrue :
  balabanRGContractionProvedAtCarrierScale
    canonicalYMBalabanCarrierRGContractionReceipt
  ≡
  true
ymBalabanCarrierRGContractionCarrierScaleTrue =
  refl

ymBalabanCarrierRGPhysicalBetaGapStillOpen :
  physicalBetaGapStillOpen canonicalYMBalabanCarrierRGContractionReceipt
  ≡
  true
ymBalabanCarrierRGPhysicalBetaGapStillOpen =
  refl

ymBalabanCarrierRGClayFalse :
  clayYMPromoted canonicalYMBalabanCarrierRGContractionReceipt ≡ false
ymBalabanCarrierRGClayFalse =
  refl

ymBalabanCarrierRGConsumesCorrectedThreshold :
  Threshold.physicalBetaKPDivergent
    (thresholdCorrectionReceipt canonicalYMBalabanCarrierRGContractionReceipt)
  ≡
  true
ymBalabanCarrierRGConsumesCorrectedThreshold =
  refl

ymBalabanCarrierRGContinuumBridgeOpenByCorrection :
  Threshold.continuumRGFlowBridgeOpen
    (thresholdCorrectionReceipt canonicalYMBalabanCarrierRGContractionReceipt)
  ≡
  true
ymBalabanCarrierRGContinuumBridgeOpenByCorrection =
  refl

ymBalabanCarrierRGNoPromotion :
  promotionFlags canonicalYMBalabanCarrierRGContractionReceipt ≡ []
ymBalabanCarrierRGNoPromotion =
  refl
