module DASHI.Reasoning.DustDirectRewardBranchExact where

-- ORIGINAL SOURCE: qlabs-eng/dust, dust.py, DUST.direct_errors
-- source implementation accessed 26 Oct 2026.
-- Authorship: Dahal, Mandal, Gülbahar, Vegesna.
-- DASHI contribution: explicit distinction between one-draw clean
-- reference and multi-draw within-chunk reward centering.
-- Source-written model; no kernel receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as Ring

half : ℚ
half = + 1 / 2

-- Raw clean-loss reduction is what the implementation evaluates first.
cleanReduction : ℚ → ℚ → ℚ
cleanReduction clean perturbed = clean + - perturbed

-- Source branch: one forward draw per chunk has no sample centering.
singletonReward : ℚ → ℚ → ℚ
singletonReward clean perturbed = cleanReduction clean perturbed

-- Source branch nrep=2: mean across the two draws is removed.
-- Hence the shared clean baseline disappears, and each result
-- equals the two-draw mean perturbed loss minus its perturbed loss.
twoDrawRewardA : ℚ → ℚ → ℚ → ℚ
twoDrawRewardA clean perturbedA perturbedB =
  cleanReduction clean perturbedA +
    - (half * (cleanReduction clean perturbedA +
                cleanReduction clean perturbedB))

twoDrawRewardB : ℚ → ℚ → ℚ → ℚ
twoDrawRewardB clean perturbedA perturbedB =
  cleanReduction clean perturbedB +
    - (half * (cleanReduction clean perturbedA +
                cleanReduction clean perturbedB))

twoDrawRewardACleanInvariant :
  (clean perturbedA perturbedB : ℚ) →
  twoDrawRewardA clean perturbedA perturbedB
    ≡ half * (perturbedB + - perturbedA)
twoDrawRewardACleanInvariant clean a b =
  Ring.solve-∀ clean a b

twoDrawRewardBCleanInvariant :
  (clean perturbedA perturbedB : ℚ) →
  twoDrawRewardB clean perturbedA perturbedB
    ≡ half * (perturbedA + - perturbedB)
twoDrawRewardBCleanInvariant clean a b =
  Ring.solve-∀ clean a b

twoDrawRewardsSumZero :
  (clean a b : ℚ) →
  twoDrawRewardA clean a b + twoDrawRewardB clean a b ≡ 0ℚ
twoDrawRewardsSumZero clean a b = Ring.solve-∀ clean a b

-- A singleton sample's raw loss reduction depends on its clean
-- reference. It is not a zero-centred reward, and its different
-- finite-K expectation must not silently inherit (K-1)/K.
singletonPreservesCleanShift :
  (clean shift perturbed : ℚ) →
  singletonReward (clean + shift) perturbed
    ≡ singletonReward clean perturbed + shift
singletonPreservesCleanShift clean shift perturbed =
  Ring.solve-∀ clean shift perturbed
