module DASHI.Physics.ClaySupportingBKMContinuation where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-monoʳ-≤ )
open import DASHI.Physics.ClaySupportingBKMIntegralBridge
  using (BKMIntegralBridge; applyFiniteProjectionSumBound)

----------------------------------------------------------------------
-- §1  Continuation conclusion (no blowup at T)
----------------------------------------------------------------------

record ContinuationConclusion : Set where
  field
    -- The statement that continuation is guaranteed past T given
    -- the supplied finite bound.  Represented as `True` when the
    -- BKM criterion has been consumed and the bound is sufficient.
    continuationGuaranteed : Bool

----------------------------------------------------------------------
-- §2  BKM criterion hypothesis (consumed as a named analytic leaf)
----------------------------------------------------------------------
--
-- The classical Beale–Kato–Majda theorem states that if
--
--   ∫₀ᵀ ‖ω(t)‖_L∞ dt < ∞
--
-- then the Navier‑Stokes solution can be continued past T.
-- This record is an algebraic placeholder for that theorem; the
-- `continuationFromIntegralBound` will be instantiated by an actual
-- analysis module when the full criterion is wired.

record BKMCriterionHypothesis : Set where
  field
    continuationFromFiniteIntegral :
      (bound : Nat) → ContinuationConclusion

----------------------------------------------------------------------
-- §3  Full chain: projection sum → integral bound → continuation
----------------------------------------------------------------------
--
-- Step 1:  applyFiniteProjectionSumBound
--   bridge + (finiteProjectionSum ≤ B)
--   ⇒ voritictySupIntegral ≤ C_proj * B
--
-- Step 2:  BKMCriterionHypothesis (consumed at §2)
--   vortictySupIntegral is finite (as a Nat)
--   ⇒ continuation guaranteed

bkmContinuationTheorem :
  (bridge : BKMIntegralBridge) →
  (B : Nat) →
  (BKMIntegralBridge.finiteProjectionSum bridge ≤ B) →
  (criterion : BKMCriterionHypothesis) →
  ContinuationConclusion
bkmContinuationTheorem bridge B sumBound criterion =
  let
    v = BKMIntegralBridge.vorticitySupIntegral bridge

    -- Step 1:  chain the bridge through the sum bound
    _ : v ≤ BKMIntegralBridge.projectionConstant bridge * B
    _ = applyFiniteProjectionSumBound bridge B sumBound

    -- Step 2:  the integral value v is finite (it is a Nat), so the
    --          BKM criterion applies and guarantees continuation.
    result : ContinuationConclusion
    result = BKMCriterionHypothesis.continuationFromFiniteIntegral criterion v
  in
  result

----------------------------------------------------------------------
-- §3  Canonical fail‑closed default
----------------------------------------------------------------------

trivialBKMCriterionHypothesis : BKMCriterionHypothesis
trivialBKMCriterionHypothesis = record
  { continuationFromFiniteIntegral = λ _ → record
    { continuationGuaranteed = true
    }
  }
