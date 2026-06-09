module DASHI.Physics.Closure.YMPaper3RoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSamePrimeOverlapReductionReceipt as YM1
import DASHI.Physics.Closure.YMBTPathCountingKPThresholdReceipt as YM23
import DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt as YM4
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt as YM5
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt as YM6

------------------------------------------------------------------------
-- Paper 3 YM dependency roadmap.
--
-- This receipt wires the YM-only roadmap:
--   YM1  same-prime overlap reduction,
--   YM2/3 BT path counting and convergence threshold,
--   YM4  strict KP absorption threshold,
--   YM5  actual Wilson polymer activity frontier,
--   YM6  Balaban RG scale-transfer frontier,
--   YM7  rho<1 / Clay-level non-promotion boundary.

data YMPaper3RoadmapStatus : Set where
  ymPaper3RoadmapRecorded :
    YMPaper3RoadmapStatus

data YMPaper3Step : Set where
  ym1SamePrimeOverlapReduction :
    YMPaper3Step

  ym2ym3BTPathCountingAndConvergence :
    YMPaper3Step

  ym4StrictKPAbsorptionThreshold :
    YMPaper3Step

  ym5ActualPolymerActivityImmediateGap :
    YMPaper3Step

  ym6BalabanRGScaleTransferHardOpen :
    YMPaper3Step

  ym7RhoBelowOneClayLevelBoundary :
    YMPaper3Step

canonicalYMPaper3Steps :
  List YMPaper3Step
canonicalYMPaper3Steps =
  ym1SamePrimeOverlapReduction
  ∷ ym2ym3BTPathCountingAndConvergence
  ∷ ym4StrictKPAbsorptionThreshold
  ∷ ym5ActualPolymerActivityImmediateGap
  ∷ ym6BalabanRGScaleTransferHardOpen
  ∷ ym7RhoBelowOneClayLevelBoundary
  ∷ []

data YMPaper3ImmediatePriority : Set where
  defineActualP7WilsonPolymerActivity :
    YMPaper3ImmediatePriority

  computeActualLocalKPRho :
    YMPaper3ImmediatePriority

  proveOrFalsifyActualRhoBelowOneAtCarrierScale :
    YMPaper3ImmediatePriority

canonicalYMPaper3ImmediatePriorities :
  List YMPaper3ImmediatePriority
canonicalYMPaper3ImmediatePriorities =
  defineActualP7WilsonPolymerActivity
  ∷ computeActualLocalKPRho
  ∷ proveOrFalsifyActualRhoBelowOneAtCarrierScale
  ∷ []

data YMPaper3NonClaim : Set where
  noToyRhoPromotion :
    YMPaper3NonClaim

  noActualKPPassYet :
    YMPaper3NonClaim

  noBalabanRGYet :
    YMPaper3NonClaim

  noContinuumYangMillsConstruction :
    YMPaper3NonClaim

  noClayYangMillsPromotion :
    YMPaper3NonClaim

canonicalYMPaper3NonClaims :
  List YMPaper3NonClaim
canonicalYMPaper3NonClaims =
  noToyRhoPromotion
  ∷ noActualKPPassYet
  ∷ noBalabanRGYet
  ∷ noContinuumYangMillsConstruction
  ∷ noClayYangMillsPromotion
  ∷ []

data YMPaper3Promotion : Set where

ymPaper3PromotionImpossibleHere :
  YMPaper3Promotion →
  ⊥
ymPaper3PromotionImpossibleHere ()

paper3RoadmapSummary :
  String
paper3RoadmapSummary =
  "Paper 3 YM roadmap: combinatorics through YM4 are recorded; YM5 actual Wilson polymer activity is the immediate gap; YM6 Balaban RG transfer is hard open; no YM/Clay promotion."

record YMPaper3RoadmapReceipt : Setω where
  field
    status :
      YMPaper3RoadmapStatus

    statusIsCanonical :
      status ≡ ymPaper3RoadmapRecorded

    ym1Receipt :
      YM1.YMSamePrimeOverlapReductionReceipt

    ym1NoClay :
      YM1.clayYangMillsPromoted ym1Receipt ≡ false

    ym23Receipt :
      YM23.YMBTPathCountingKPThresholdReceipt

    ym23NoStrictAbsorption :
      YM23.strictAbsorptionMarginProved ym23Receipt ≡ false

    ym23P7ConvergenceThresholdNumerator :
      YM23.p7ConvergenceBetaNumeratorRecorded ym23Receipt
      ≡
      YM23.p7ConvergenceBetaNumerator

    ym23P7ConvergenceThresholdDenominator :
      YM23.p7ConvergenceBetaDenominatorRecorded ym23Receipt
      ≡
      YM23.p7ConvergenceBetaDenominator

    ym4Receipt :
      YM4.YMKPAbsorptionMarginThresholdReceipt

    ym4ActualRhoStillOpen :
      YM4.actualRhoMarginProved ym4Receipt ≡ false

    ym4StrictAbsorptionLaw :
      YM4.marginLaw ym4Receipt
      ≡
      YM4.localSumBelowOneRequiresLogTwoP

    ym4ConvergenceWeakerThanAbsorption :
      YM4.seriesVerdict ym4Receipt
      ≡
      YM4.convergenceIsWeakerThanAbsorption

    ym4P7AbsorptionThresholdNumerator :
      YM4.p7AbsorptionBetaNumeratorRecorded ym4Receipt
      ≡
      YM4.p7AbsorptionBetaNumerator

    ym4P7AbsorptionThresholdDenominator :
      YM4.p7AbsorptionBetaDenominatorRecorded ym4Receipt
      ≡
      YM4.p7AbsorptionBetaDenominator

    ym5Receipt :
      YM5.YMActualPolymerActivityDefinitionReceipt

    ym5ActualActivityStillMissing :
      YM5.actualPolymerActivitySupplied ym5Receipt ≡ false

    ym5ToyRhoRejected :
      YM5.rejectedRhoSource ym5Receipt ≡ YM5.toyDepthProfile

    ym5ActualWilsonRhoRequired :
      YM5.requiredRhoSource ym5Receipt ≡ YM5.actualWilsonPolymerActivity

    ym5ToyRhoNotPromoted :
      YM5.toyRhoPromotedAsKPProof ym5Receipt ≡ false

    ym6Receipt :
      YM6.YMBalabanRGScaleTransferFrontierReceipt

    ym6BalabanStillMissing :
      YM6.balabanRGProofPresent ym6Receipt ≡ false

    ym6StrictMarginThresholdNumerator :
      YM6.strictMarginBetaNumeratorRecorded ym6Receipt
      ≡
      YM6.strictKPMarginBetaNumerator

    ym6StrictMarginThresholdDenominator :
      YM6.strictMarginBetaDenominatorRecorded ym6Receipt
      ≡
      YM6.strictKPMarginBetaDenominator

    ym6OpenGapIsNonperturbativeBridge :
      YM6.bridgeVerdict ym6Receipt ≡ YM6.nonperturbativeBridgeRequired

    roadmapSteps :
      List YMPaper3Step

    roadmapStepsAreCanonical :
      roadmapSteps ≡ canonicalYMPaper3Steps

    immediatePriorities :
      List YMPaper3ImmediatePriority

    immediatePrioritiesAreCanonical :
      immediatePriorities ≡ canonicalYMPaper3ImmediatePriorities

    nonClaims :
      List YMPaper3NonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMPaper3NonClaims

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
      summary ≡ paper3RoadmapSummary

open YMPaper3RoadmapReceipt public

canonicalYMPaper3RoadmapReceipt :
  YMPaper3RoadmapReceipt
canonicalYMPaper3RoadmapReceipt =
  record
    { status =
        ymPaper3RoadmapRecorded
    ; statusIsCanonical =
        refl
    ; ym1Receipt =
        YM1.canonicalYMSamePrimeOverlapReductionReceipt
    ; ym1NoClay =
        refl
    ; ym23Receipt =
        YM23.canonicalYMBTPathCountingKPThresholdReceipt
    ; ym23NoStrictAbsorption =
        refl
    ; ym23P7ConvergenceThresholdNumerator =
        refl
    ; ym23P7ConvergenceThresholdDenominator =
        refl
    ; ym4Receipt =
        YM4.canonicalYMKPAbsorptionMarginThresholdReceipt
    ; ym4ActualRhoStillOpen =
        refl
    ; ym4StrictAbsorptionLaw =
        refl
    ; ym4ConvergenceWeakerThanAbsorption =
        refl
    ; ym4P7AbsorptionThresholdNumerator =
        refl
    ; ym4P7AbsorptionThresholdDenominator =
        refl
    ; ym5Receipt =
        YM5.canonicalYMActualPolymerActivityDefinitionReceipt
    ; ym5ActualActivityStillMissing =
        refl
    ; ym5ToyRhoRejected =
        refl
    ; ym5ActualWilsonRhoRequired =
        refl
    ; ym5ToyRhoNotPromoted =
        refl
    ; ym6Receipt =
        YM6.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; ym6BalabanStillMissing =
        refl
    ; ym6StrictMarginThresholdNumerator =
        refl
    ; ym6StrictMarginThresholdDenominator =
        refl
    ; ym6OpenGapIsNonperturbativeBridge =
        refl
    ; roadmapSteps =
        canonicalYMPaper3Steps
    ; roadmapStepsAreCanonical =
        refl
    ; immediatePriorities =
        canonicalYMPaper3ImmediatePriorities
    ; immediatePrioritiesAreCanonical =
        refl
    ; nonClaims =
        canonicalYMPaper3NonClaims
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
        paper3RoadmapSummary
    ; summaryIsCanonical =
        refl
    }
