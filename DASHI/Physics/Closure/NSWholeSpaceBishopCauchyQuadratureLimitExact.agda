module DASHI.Physics.Closure.NSWholeSpaceBishopCauchyQuadratureLimitExact where

------------------------------------------------------------------------
-- A / WEIGHTED CAUCHY QUADRATURE -> CONTINUOUS PSD
--
-- The finite PSD theorem is now instantiated on literal weighted quadrature
-- cells.  The only remaining analytic datum is convergence of those concrete
-- finite quadrature forms to the selected continuous Cauchy Gram.
--
-- This is strictly narrower than accepting an arbitrary finite form plus a
-- separate same-object meaning proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Physics.Closure.NSWholeSpaceBishopCauchyPSDLimitExact as Limit
import DASHI.Physics.Closure.NSWholeSpaceBishopWeightedCauchyQuadraturePSDExact as Weighted

record WeightedCauchyQuadratureApproximation
    (continuousCauchyGram : BishopReal.ℝ) : Set₁ where
  constructor weighted-cauchy-quadrature-approximation
  field
    quadratureCells :
      Nat → List Weighted.WeightedPositiveRateComplex3Cell

    quadratureFormsConverge :
      BishopSequence._ConvergesTo_
        (λ index →
          Weighted.weightedHermitianCauchyForm
            (quadratureCells index))
        continuousCauchyGram

open WeightedCauchyQuadratureApproximation public

asFiniteCauchyApproximation :
  ∀ {continuousCauchyGram} →
  WeightedCauchyQuadratureApproximation continuousCauchyGram →
  Limit.FiniteCauchyApproximationToContinuous continuousCauchyGram
asFiniteCauchyApproximation A =
  Limit.finite-cauchy-approximation-to-continuous
    (λ index →
      Weighted.weightedCells
        (quadratureCells A index))
    (λ index →
      Weighted.weightedHermitianCauchyForm
        (quadratureCells A index))
    (λ index → refl)
    (quadratureFormsConverge A)

continuousWeightedCauchyGramNonnegative :
  ∀ {continuousCauchyGram} →
  WeightedCauchyQuadratureApproximation continuousCauchyGram →
  BishopReal.NonNegative continuousCauchyGram
continuousWeightedCauchyGramNonnegative A =
  Limit.continuousCauchyGramNonnegative
    (asFiniteCauchyApproximation A)

weightedQuadratureToContinuousPSDClosed : Bool
weightedQuadratureToContinuousPSDClosed = true

arbitraryFiniteFormMeaningRequired : Bool
arbitraryFiniteFormMeaningRequired = false

remainingInputIsLiteralQuadratureConvergence : Bool
remainingInputIsLiteralQuadratureConvergence = true

clayPromotion : Bool
clayPromotion = false

weightedQuadratureToContinuousPSDClosedIsTrue :
  weightedQuadratureToContinuousPSDClosed ≡ true
weightedQuadratureToContinuousPSDClosedIsTrue = refl

arbitraryFiniteFormMeaningRequiredIsFalse :
  arbitraryFiniteFormMeaningRequired ≡ false
arbitraryFiniteFormMeaningRequiredIsFalse = refl

remainingInputIsLiteralQuadratureConvergenceIsTrue :
  remainingInputIsLiteralQuadratureConvergence ≡ true
remainingInputIsLiteralQuadratureConvergenceIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
