{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelToAugmentedShootingExact where

------------------------------------------------------------------------
-- ROW A: RESPONSE-KERNEL SUMMATION -> EXISTING AUGMENTED SHOOTING GATE
--
-- The response-kernel compiler gives the exact cutoff-uniform history constant
--
--       q_history = 2 C_response S_total.
--
-- This file feeds that constant directly into the existing direct+history
-- shooting theorem.  Unlike the alternative O(gamma) initial-response route,
-- no assumption is made here about how S_total scales with gamma.  The only
-- scalar condition is the one the actual shooting consumer needs:
--
--   L_local * gamma_tube + b_* * (2 C_response S_total) < b_*.
--
-- This mirrors the parallel Lean `RowASensitivityFromResponse` architecture and
-- gives us two source routes to the same completion consumer.  Whichever source
-- estimate is weaker/easier should be used; neither is promoted by bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

responseHistoryConstant :
  ∀ {kernel} → Kernel.UniformSourceSensitivityBudget kernel → ℚ
responseHistoryConstant {kernel} budget =
  Geo.twoℚ * Kernel.responseCoefficient kernel
    * Kernel.totalSourceSensitivity budget

responseHistoryConstantNonnegative :
  ∀ {kernel}
    (budget : Kernel.UniformSourceSensitivityBudget kernel) →
  0ℚ ≤ responseHistoryConstant budget
responseHistoryConstantNonnegative {kernel} budget =
  let
    twoNN : 0ℚ ≤ Geo.twoℚ
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof

    instance
      twoNonnegative : NonNegative Geo.twoℚ
      twoNonnegative = ℚ.nonNegative twoNN
      coefficientNonnegative : NonNegative (Kernel.responseCoefficient kernel)
      coefficientNonnegative =
        ℚ.nonNegative (Kernel.responseCoefficientNonnegative kernel)
      totalNonnegative : NonNegative (Kernel.totalSourceSensitivity budget)
      totalNonnegative =
        ℚ.nonNegative (Kernel.totalSourceSensitivityNonnegative budget)

    firstNN : NonNegative (Geo.twoℚ * Kernel.responseCoefficient kernel)
    firstNN = ℚP.nonNeg*nonNeg⇒nonNeg
      Geo.twoℚ (Kernel.responseCoefficient kernel)

    instance firstNonnegative = firstNN
  in
  ℚP.nonNegative⁻¹
    ((Geo.twoℚ * Kernel.responseCoefficient kernel)
      * Kernel.totalSourceSensitivity budget)

record ResponseKernelAugmentedShootingData (cutoff : Nat) : Set₁ where
  field
    direct : Direct.CumulativeSensitivityData cutoff
    kernel : Kernel.GeometricBetaResponseKernel
    sourceBudget : Kernel.UniformSourceSensitivityBudget kernel

    responseAugmentedGate :
      Direct.derivativeBound direct * Direct.tubeWidth direct
        + Direct.marginConstant direct
            * responseHistoryConstant sourceBudget
      < Direct.marginConstant direct

open ResponseKernelAugmentedShootingData public

asAugmentedShootingData :
  ∀ {cutoff} →
  ResponseKernelAugmentedShootingData cutoff →
  Aug.AugmentedShootingSensitivityData cutoff
asAugmentedShootingData dataSet = record
  { Aug.AugmentedShootingSensitivityData.direct = direct dataSet
  ; Aug.AugmentedShootingSensitivityData.historyConstant =
      responseHistoryConstant (sourceBudget dataSet)
  ; Aug.AugmentedShootingSensitivityData.historyConstantNonnegative =
      responseHistoryConstantNonnegative (sourceBudget dataSet)
  ; Aug.AugmentedShootingSensitivityData.augmentedContractionGate =
      responseAugmentedGate dataSet
  }

responseKernelCumulativeHistoryBound :
  ∀ {cutoff}
    (dataSet : ResponseKernelAugmentedShootingData cutoff) K →
  Kernel.sum₀ (Kernel.responseSensitivity (kernel dataSet)) K
  ≤ responseHistoryConstant (sourceBudget dataSet)
responseKernelCumulativeHistoryBound dataSet =
  Kernel.uniformCumulativeResponse (sourceBudget dataSet)

responseKernelTotalShootingSensitivityBelowOne :
  ∀ {cutoff}
    (dataSet : ResponseKernelAugmentedShootingData cutoff)
    K → K ℕ.≤ cutoff →
  Aug.Augmented.qTotal (asAugmentedShootingData dataSet) K
  < 1ℚ
responseKernelTotalShootingSensitivityBelowOne dataSet =
  Aug.Augmented.qTotalBelowOne (asAugmentedShootingData dataSet)

rowAResponseKernelToHistoryConstantLevel : ProofLevel
rowAResponseKernelToHistoryConstantLevel = machineChecked

rowAResponseKernelToAugmentedShootingLevel : ProofLevel
rowAResponseKernelToAugmentedShootingLevel = machineChecked

-- Physical/source leaf for this route:
--  1. literal same-history response satisfies the geometric one-step kernel;
--  2. direct source sensitivities have one cutoff-uniform total budget S_total;
--  3. the resulting explicit scalar response gate is strict on the same tube.
-- This is an alternative to the stronger `initial response = O(gamma)` route.
literalRowAResponseKernelShootingInstantiationLevel : ProofLevel
literalRowAResponseKernelShootingInstantiationLevel = conditional
