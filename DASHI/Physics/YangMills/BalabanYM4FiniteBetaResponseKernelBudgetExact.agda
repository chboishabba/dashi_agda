{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4FiniteBetaResponseKernelBudgetExact where

------------------------------------------------------------------------
-- ROW A: CUTOFF-INDEXED VERSION OF THE RESPONSE-KERNEL BUDGET
--
-- The literal Bałaban trajectory at fixed UV cutoff is finite.  Requiring a
-- source sensitivity budget for every natural K is stronger than the consumer
-- needs.  This adapter keeps the exact response-kernel theorem but weakens the
-- source premise to
--
--        K <= cutoff  ==>  sum_{j<K} s_j <= S_total.
--
-- This is the correct backwards contract for the finite-cutoff shooting map.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel

record FiniteSourceSensitivityBudget
    (kernel : Kernel.GeometricBetaResponseKernel)
    (cutoff : Nat) : Set where
  field
    totalSourceSensitivity : ℚ
    totalSourceSensitivityNonnegative : 0ℚ ≤ totalSourceSensitivity
    sourcePartialBelowTotal : ∀ K → K ℕ.≤ cutoff →
      Kernel.sum₀ (Kernel.sourceSensitivity kernel) K
      ≤ totalSourceSensitivity

open FiniteSourceSensitivityBudget public

finiteUniformCumulativeResponse :
  ∀ {kernel cutoff}
    (budget : FiniteSourceSensitivityBudget kernel cutoff)
    K → K ℕ.≤ cutoff →
  Kernel.sum₀ (Kernel.responseSensitivity kernel) K
  ≤ Geo.twoℚ * Kernel.responseCoefficient kernel
      * totalSourceSensitivity budget
finiteUniformCumulativeResponse {kernel} budget K K≤ =
  let
    coefficientNN : 0ℚ ≤ Geo.twoℚ * Kernel.responseCoefficient kernel
    coefficientNN =
      let
        twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
        instance
          twoNonnegative : NonNegative Geo.twoℚ
          twoNonnegative = ℚ.nonNegative twoNN
          cNonnegative : NonNegative (Kernel.responseCoefficient kernel)
          cNonnegative = ℚ.nonNegative
            (Kernel.responseCoefficientNonnegative kernel)
      in
      ℚP.nonNegative⁻¹ (Geo.twoℚ * Kernel.responseCoefficient kernel)

    scaled = Norm.scaleNonnegative
      (Geo.twoℚ * Kernel.responseCoefficient kernel)
      coefficientNN
      (sourcePartialBelowTotal budget K K≤)
  in
  ℚP.≤-trans
    (Kernel.cumulativeResponseBelowScaledSource kernel K)
    scaled

finiteBetaResponseKernelBudgetLevel : ProofLevel
finiteBetaResponseKernelBudgetLevel = machineChecked

-- Physical source seam is now finite-cutoff exact: prove the direct source
-- sensitivity partial sums are uniformly bounded for K <= cutoff.  No claim is
-- required outside the generated finite RG history.
literalFiniteBetaSourceSensitivityBudgetLevel : ProofLevel
literalFiniteBetaSourceSensitivityBudgetLevel = conditional
