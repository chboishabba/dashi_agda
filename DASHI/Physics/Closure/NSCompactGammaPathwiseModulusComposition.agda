module DASHI.Physics.Closure.NSCompactGammaPathwiseModulusComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Local-to-global composition for a path partition.
--
-- `AdditiveModulusStep` is the abstract Gamma estimate
--
--   end <= start + allowance.
--
-- `RetainedEscapeStep` is the positive escape estimate
--
--   retain(start) <= end.
--
-- The concrete real-number audit uses an additive Gamma allowance and a
-- multiplicative escape retention.  This module proves that adjacent local
-- estimates compose.  It does not construct any analytic modulus.
------------------------------------------------------------------------

record AdditiveModulusStep
    (A : AbsorptionArithmetic) : Set₁ where
  field
    startValue : Scalar A
    endValue : Scalar A
    allowance : Scalar A

    endBelowStartPlusAllowance :
      _≤_ A endValue (_+_ A startValue allowance)

open AdditiveModulusStep public

combineAdditiveModulusSteps :
  (A : AbsorptionArithmetic) →
  (left right : AdditiveModulusStep A) →
  endValue left ≡ startValue right →
  AdditiveModulusStep A
combineAdditiveModulusSteps A left right middleMatches = record
  { startValue = startValue left
  ; endValue = endValue right
  ; allowance = _+_ A (allowance left) (allowance right)
  ; endBelowStartPlusAllowance = end≤combinedUpper
  }
  where
  rightEnd≤leftEndPlusRightAllowance :
    _≤_ A
      (endValue right)
      (_+_ A (endValue left) (allowance right))
  rightEnd≤leftEndPlusRightAllowance =
    subst
      (λ middle →
        _≤_ A (endValue right)
          (_+_ A middle (allowance right)))
      (sym middleMatches)
      (endBelowStartPlusAllowance right)

  leftEndPlusRightAllowance≤rawUpper :
    _≤_ A
      (_+_ A (endValue left) (allowance right))
      (_+_ A
        (_+_ A (startValue left) (allowance left))
        (allowance right))
  leftEndPlusRightAllowance≤rawUpper =
    additionMonotoneRight A
      (endBelowStartPlusAllowance left)

  rightEnd≤rawUpper :
    _≤_ A
      (endValue right)
      (_+_ A
        (_+_ A (startValue left) (allowance left))
        (allowance right))
  rightEnd≤rawUpper =
    ≤-trans A
      rightEnd≤leftEndPlusRightAllowance
      leftEndPlusRightAllowance≤rawUpper

  end≤combinedUpper :
    _≤_ A
      (endValue right)
      (_+_ A
        (startValue left)
        (_+_ A (allowance left) (allowance right)))
  end≤combinedUpper =
    subst
      (λ upper → _≤_ A (endValue right) upper)
      (addAssociative A
        (startValue left)
        (allowance left)
        (allowance right))
      rightEnd≤rawUpper

record RetainedEscapeStep
    (A : AbsorptionArithmetic) : Set₁ where
  field
    startEscape : Scalar A
    endEscape : Scalar A

    retain : Scalar A → Scalar A

    retainMonotone :
      {left right : Scalar A} →
      _≤_ A left right →
      _≤_ A (retain left) (retain right)

    retainedStartBelowEnd :
      _≤_ A (retain startEscape) endEscape

open RetainedEscapeStep public

combineRetainedEscapeSteps :
  (A : AbsorptionArithmetic) →
  (left right : RetainedEscapeStep A) →
  endEscape left ≡ startEscape right →
  RetainedEscapeStep A
combineRetainedEscapeSteps A left right middleMatches = record
  { startEscape = startEscape left
  ; endEscape = endEscape right
  ; retain = λ value → retain right (retain left value)
  ; retainMonotone = λ order →
      retainMonotone right (retainMonotone left order)
  ; retainedStartBelowEnd = composedRetention
  }
  where
  retainedTwice≤rightRetainedMiddle :
    _≤_ A
      (retain right (retain left (startEscape left)))
      (retain right (endEscape left))
  retainedTwice≤rightRetainedMiddle =
    retainMonotone right (retainedStartBelowEnd left)

  rightRetainedMiddle≤end :
    _≤_ A
      (retain right (endEscape left))
      (endEscape right)
  rightRetainedMiddle≤end =
    subst
      (λ middle →
        _≤_ A (retain right middle) (endEscape right))
      (sym middleMatches)
      (retainedStartBelowEnd right)

  composedRetention :
    _≤_ A
      (retain right (retain left (startEscape left)))
      (endEscape right)
  composedRetention =
    ≤-trans A
      retainedTwice≤rightRetainedMiddle
      rightRetainedMiddle≤end
