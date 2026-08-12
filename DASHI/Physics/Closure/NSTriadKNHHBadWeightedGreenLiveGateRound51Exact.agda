module DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenLiveGateRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 51's weighted Green response is the least over-specified recurrence
-- consumer currently available.  If
--
--   C_0 + B_weighted < T,
--   T = 15/32 - (tau_Com + tau_kernel)/2,
--
-- then the resulting HH-bad ceiling feeds the same H2<1 gate as the earlier
-- strict-contraction and raw-summable routes.  With soft Com/kernel this is
-- simply C_0 + B_weighted < 15/32.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenToOwnerRound51Exact as GreenOwner

record WeightedGreenLiveBudgetInput : Set where
  field
    recurrenceInput : Green.VariableGreenRecurrence
    weightedBound : Green.UniformWeightedGreenBound recurrenceInput
    comFloor kernelFloor : ℚ
    weightedCeilingBelowLiveTarget :
      GreenOwner.weightedGreenCeiling weightedBound
      < Live.allowableHHBadCeiling comFloor kernelFloor

open WeightedGreenLiveBudgetInput public

weightedGreenImpliesH2Strict :
  (input : WeightedGreenLiveBudgetInput) →
  Gate.hardGateH2
    (GreenOwner.weightedGreenCeiling (weightedBound input))
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
weightedGreenImpliesH2Strict input =
  Live.liveCeilingTargetImpliesH2Strict
    (GreenOwner.weightedGreenCeiling (weightedBound input))
    (comFloor input)
    (kernelFloor input)
    (weightedCeilingBelowLiveTarget input)

record SoftComKernelWeightedGreenInput : Set where
  field
    recurrenceInput : Green.VariableGreenRecurrence
    weightedBound : Green.UniformWeightedGreenBound recurrenceInput
    basePlusWeightedBelowFifteenThirtySeconds :
      GreenOwner.weightedGreenCeiling weightedBound
      < Live.fifteenThirtySeconds

open SoftComKernelWeightedGreenInput public

softComKernelWeightedLiveInput :
  SoftComKernelWeightedGreenInput → WeightedGreenLiveBudgetInput
softComKernelWeightedLiveInput input = record
  { recurrenceInput = SoftComKernelWeightedGreenInput.recurrenceInput input
  ; weightedBound = SoftComKernelWeightedGreenInput.weightedBound input
  ; comFloor = 0ℚ
  ; kernelFloor = 0ℚ
  ; weightedCeilingBelowLiveTarget =
      subst
        (λ upper →
          GreenOwner.weightedGreenCeiling
            (SoftComKernelWeightedGreenInput.weightedBound input)
          < upper)
        (sym Live.allowableWithSoftComAndKernel)
        (basePlusWeightedBelowFifteenThirtySeconds input)
  }

softComKernelWeightedGreenImpliesH0Strict :
  (input : SoftComKernelWeightedGreenInput) →
  Gate.hardGateH2
    (GreenOwner.weightedGreenCeiling
      (SoftComKernelWeightedGreenInput.weightedBound input))
    0ℚ 0ℚ
  < 1ℚ
softComKernelWeightedGreenImpliesH0Strict input =
  weightedGreenImpliesH2Strict (softComKernelWeightedLiveInput input)

data HHBadPhysicalRoute51 : Set where
  strictContraction rawSummable weightedGreen : HHBadPhysicalRoute51

weightedGreenIsMasterHHBadFallback : Bool
weightedGreenIsMasterHHBadFallback = true

weightedGreenIsMasterHHBadFallbackIsTrue :
  weightedGreenIsMasterHHBadFallback ≡ true
weightedGreenIsMasterHHBadFallbackIsTrue = refl
