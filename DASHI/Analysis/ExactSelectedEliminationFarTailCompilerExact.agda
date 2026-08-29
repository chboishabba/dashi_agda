module DASHI.Analysis.ExactSelectedEliminationFarTailCompilerExact where

------------------------------------------------------------------------
-- EXACT SELECTED ELIMINATION + FAR-TAIL PAYMENT
--
-- Once a finite selected nuisance carrier is eliminated exactly, there is no
-- selected/local residual debt to pay.  The quantitative admission interface
-- should therefore expose only the projected far remainder:
--
--     farResidual <= farBudget < strictSignalMargin.
--
-- This is a specialization of the generic residual-budget architecture, not a
-- new analytic estimate.  A domain owner must still prove the literal far-tail
-- bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

record ExactSelectedFarTailMargin : Set where
  constructor exact-selected-far-tail-margin
  field
    selectedCarrierSize : Nat
    farResidual farBudget strictSignalMargin : ℚ
    selectedResidualIsExactlyZero : Bool
    selectedResidualIsExactlyZeroIsTrue : selectedResidualIsExactlyZero ≡ true
    farResidualBound : farResidual ≤ farBudget
    farBudgetBelowStrictMargin : farBudget < strictSignalMargin

open ExactSelectedFarTailMargin public

farResidualStrictlyBelowSignalMargin :
  (d : ExactSelectedFarTailMargin) →
  farResidual d < strictSignalMargin d
farResidualStrictlyBelowSignalMargin d =
  ℚP.≤-<-trans (farResidualBound d) (farBudgetBelowStrictMargin d)

record ExactSelectedFarTailBoundary : Set where
  constructor exact-selected-far-tail-boundary
  field
    selectedResidualNeedsSeparateBudget : Bool
    selectedResidualNeedsSeparateBudgetIsFalse :
      selectedResidualNeedsSeparateBudget ≡ false
    farTailEstimateProducedByCompiler : Bool
    farTailEstimateProducedByCompilerIsFalse :
      farTailEstimateProducedByCompiler ≡ false
    exactFiniteEliminationSolvesInfiniteTail : Bool
    exactFiniteEliminationSolvesInfiniteTailIsFalse :
      exactFiniteEliminationSolvesInfiniteTail ≡ false

canonicalExactSelectedFarTailBoundary : ExactSelectedFarTailBoundary
canonicalExactSelectedFarTailBoundary =
  exact-selected-far-tail-boundary false refl false refl false refl
