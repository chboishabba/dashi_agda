module DASHI.Analysis.RiemannAristotleTargetRemainderMarginCompilerExact where

------------------------------------------------------------------------
-- BIDI CORRECTION: DO NOT BUDGET THE WHOLE POST-SCHUR OFF CARRIER BELOW
-- ITS OWN SURVIVING MARGIN.
--
-- If the deterministic Schur identity identifies
--
--   E D_cluster = E D_off,
--
-- then demanding an upper bound B on ||E D_off||^2 with
--
--   B < ||E D_cluster||^2
--
-- is impossible: those are the same number.  The correct strict-budget target
-- must first split the zero carrier into
--
--   target same-ordinate contribution + genuine remainder,
--
-- and budget only the remainder.
--
-- This file owns the order-theoretic compiler.  The domain-specific Lean owner
-- must provide the literal target/remainder decomposition and the norm/triangle
-- consequence that converts exact balance into
--
--   targetMagnitude <= remainderMagnitude.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

wholeCarrierStrictBudgetImpossible :
  ∀ {whole budget : ℚ} →
  whole ≤ budget →
  budget < whole →
  ⊥
wholeCarrierStrictBudgetImpossible whole≤budget budget<whole =
  ℚP.<-irrefl refl (ℚP.<-≤-trans budget<whole whole≤budget)

record TargetRemainderMargin : Set where
  constructor target-remainder-margin
  field
    targetMagnitude remainderMagnitude remainderBudget targetLowerMargin : ℚ

    targetLowerBound : targetLowerMargin ≤ targetMagnitude

    -- Produced by the literal exact balance after all deterministic nuisance
    -- channels are eliminated.  For example, target + remainder = 0 implies
    -- equal norms/magnitudes in the one-dimensional residual lane, or at least
    -- targetMagnitude <= remainderMagnitude via a domain-specific norm lemma.
    balanceForcesTargetIntoRemainder : targetMagnitude ≤ remainderMagnitude

    remainderBound : remainderMagnitude ≤ remainderBudget
    remainderBudgetBelowTargetMargin : remainderBudget < targetLowerMargin

open TargetRemainderMargin public

targetRemainderMarginContradiction :
  (d : TargetRemainderMargin) → ⊥
targetRemainderMarginContradiction d =
  let
    target≤budget : targetMagnitude d ≤ remainderBudget d
    target≤budget = ℚP.≤-trans
      (balanceForcesTargetIntoRemainder d)
      (remainderBound d)

    margin≤budget : targetLowerMargin d ≤ remainderBudget d
    margin≤budget = ℚP.≤-trans
      (targetLowerBound d)
      target≤budget
  in
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans (remainderBudgetBelowTargetMargin d) margin≤budget)

record TargetRemainderBoundary : Set where
  constructor target-remainder-boundary
  field
    wholePostSchurCarrierMayBeBudgetedBelowItself : Bool
    wholePostSchurCarrierMayBeBudgetedBelowItselfIsFalse :
      wholePostSchurCarrierMayBeBudgetedBelowItself ≡ false
    strictBudgetMustApplyOnlyToGenuineRemainder : Bool
    strictBudgetMustApplyOnlyToGenuineRemainderIsTrue :
      strictBudgetMustApplyOnlyToGenuineRemainder ≡ true
    absoluteConvergenceAloneSuppliesStrictCancellation : Bool
    absoluteConvergenceAloneSuppliesStrictCancellationIsFalse :
      absoluteConvergenceAloneSuppliesStrictCancellation ≡ false

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalTargetRemainderBoundary : TargetRemainderBoundary
canonicalTargetRemainderBoundary =
  target-remainder-boundary false refl true refl false refl
