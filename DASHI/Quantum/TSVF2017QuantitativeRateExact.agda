{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017QuantitativeRateExact where

-- QUANTIFIED ROBUSTNESS AS A REAL ALL-k MATHEMATICAL THEOREM.
--
-- Prior SOURCE-WRITTEN original TSVF ABL model: selected right/wrong Born
-- numerators are 25^k and 9^k (k=N-n surviving independent record sites).
-- We now prove, FOR ALL k, 25^k >= 2^k*9^k. Thus the EXACT ABL odds
-- grow at least 2^k, with no limiting/experimental extrapolation.
-- General positive disturbance-weight comparison gammaR>=gammaW gives
-- gammaR*25^k >= 2^k*(gammaW*9^k); resulting wrong probability is
-- <=1/(2^k+1), presented with a positive-denominator cross inequality.
--
-- The key hypothesis gammaR>=gammaW is NOT established by N>>n alone.
-- In the ACTUAL 2017 paper gamma_j are environment overlap AMPLITUDES;
-- the source must prove a bound on their squared magnitudes first.
-- This Nat-valued rate is a rigorous finite-source specialization, NOT
-- a physical macroscopic time reversal or a uniform continuum OS gap.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as Finite

power : Nat → Nat → Nat
power = Finite.power

eighteenAtMost25 : 18 ≤ 25
eighteenAtMost25 = ℕₚ.m≤m+n 18 7

powerMonotone :
  ∀ (a b k : Nat) → a ≤ b → power a k ≤ power b k
powerMonotone a b zero order = ℕₚ.≤-refl
powerMonotone a b (suc k) order =
  ℕₚ.*-mono-≤ order (powerMonotone a b k order)

-- Every remaining pointer/environment site gives at least a factor-two
-- ratio advantage under the original concrete 3/5 overlap model.
doublingRightVsWrongForAllK :
  (k : Nat) →
  power 2 k * Finite.wrongRaw k ≤ Finite.rightRaw k
doublingRightVsWrongForAllK k
  rewrite Finite.tensorPowerMultiplicative 2 9 k =
  powerMonotone 18 25 k eighteenAtMost25

swapTwoFactors :
  (a b c : Nat) →
  a * (b * c) ≡ b * (a * c)
swapTwoFactors a b c =
  trans
    (sym (ℕₚ.*-assoc a b c))
    (trans
      (cong (λ v → v * c) (ℕₚ.*-comm a b))
      (ℕₚ.*-assoc b a c))

-- The strong *physical* condition here is explicitly the nonnegative
-- disturbed Born-weight ordering (a consequence of complex gamma controls
-- only if the source proves it).
weightedDoublingBound :
  (gammaRight gammaWrong k : Nat) →
  gammaWrong ≤ gammaRight →
  power 2 k * (gammaWrong * Finite.wrongRaw k)
  ≤ gammaRight * Finite.rightRaw k
weightedDoublingBound gammaRight gammaWrong k order
  rewrite swapTwoFactors (power 2 k) gammaWrong
    (Finite.wrongRaw k) =
  ℕₚ.*-mono-≤ order (doublingRightVsWrongForAllK k)

rightWrongTotal : Nat → Nat → Nat → Nat
rightWrongTotal gammaRight gammaWrong k =
  gammaRight * Finite.rightRaw k
    + gammaWrong * Finite.wrongRaw k

-- Common-denominator statement of
--
--    P_wrong ≤ 1 / (2^k+1)
--
-- whenever gammaWrong≤gammaRight and the selected total is positive.
-- It deliberately avoids division and is valid even for gammaWrong=0.
wrongProbabilityExponentialDenominatorBound :
  (gammaRight gammaWrong k : Nat) →
  gammaWrong ≤ gammaRight →
  (power 2 k + 1) * (gammaWrong * Finite.wrongRaw k)
    ≤ rightWrongTotal gammaRight gammaWrong k
wrongProbabilityExponentialDenominatorBound gammaRight gammaWrong k order
  rewrite ℕₚ.*-distribʳ-+ (power 2 k) 1
    (gammaWrong * Finite.wrongRaw k)
        | ℕₚ.*-identityˡ (gammaWrong * Finite.wrongRaw k) =
  ℕₚ.+-mono-≤
    (weightedDoublingBound gammaRight gammaWrong k order)
    ℕₚ.≤-refl

-- At k=0 the universal guarantee is only P_R ≥ P_W and no stronger
-- macroscopic claim; after one site, the bound is at least two-to-one.
zeroSiteHasNoStrictAdvantage :
  Finite.rightRaw 0 ≡ Finite.wrongRaw 0
zeroSiteHasNoStrictAdvantage = refl

oneSiteRightTwentyFiveWrongNine :
  (Finite.rightRaw 1 ≡ 25)
  × (Finite.wrongRaw 1 ≡ 9)
oneSiteRightTwentyFiveWrongNine = refl , refl

-- The inequality need not hold when the physical gamma-order premise is
-- violated: from the original exact adversarial fixture gammaR=1,
-- gammaW=100, k=2, wrong=8100 > right=625.
adversarialNoGammaControl :
  625 ≤ 8100
adversarialNoGammaControl = ℕₚ.m≤m+n 625 7475
