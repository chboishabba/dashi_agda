module DASHI.Reasoning.DustHeadBatchCenteringExact where

-- Exact branch of the original qlabs-eng/dust dust.py head_error:
-- reward is centered ACROSS BATCH if b > 1, independently of nrep.
-- Original algorithm: Dahal/Mandal/Gülbahar/Vegesna.
-- DASHI: rational two-item specialization and obstruction.
-- Agda source candidate, no kernel execution receipt.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as Ring

half : ℚ
half = + 1 / 2

headCleanReduction : ℚ → ℚ → ℚ
headCleanReduction clean noisy = clean + - noisy

-- Two different examples within one draw, not two independent probes.
centeredHeadA : ℚ → ℚ → ℚ → ℚ → ℚ
centeredHeadA cleanA cleanB noisyA noisyB =
  headCleanReduction cleanA noisyA +
    - (half * (headCleanReduction cleanA noisyA +
               headCleanReduction cleanB noisyB))

centeredHeadB : ℚ → ℚ → ℚ → ℚ → ℚ
centeredHeadB cleanA cleanB noisyA noisyB =
  headCleanReduction cleanB noisyB +
    - (half * (headCleanReduction cleanA noisyA +
               headCleanReduction cleanB noisyB))

headTwoBatchZeroSum :
  (cleanA cleanB noisyA noisyB : ℚ) →
  centeredHeadA cleanA cleanB noisyA noisyB +
    centeredHeadB cleanA cleanB noisyA noisyB ≡ 0ℚ
headTwoBatchZeroSum cA cB nA nB = Ring.solve-∀ cA cB nA nB

-- Batch centering is NOT clean-reference invariant independently for
-- each example. A change in cleanA alters both batch rewards.
headBatchCleanShiftA :
  (cA cB nA nB shift : ℚ) →
  centeredHeadA (cA + shift) cB nA nB
    ≡ centeredHeadA cA cB nA nB + half * shift
headBatchCleanShiftA cA cB nA nB shift =
  Ring.solve-∀ cA cB nA nB shift

headBatchCleanShiftB :
  (cA cB nA nB shift : ℚ) →
  centeredHeadB (cA + shift) cB nA nB
    ≡ centeredHeadB cA cB nA nB + - (half * shift)
headBatchCleanShiftB cA cB nA nB shift =
  Ring.solve-∀ cA cB nA nB shift
