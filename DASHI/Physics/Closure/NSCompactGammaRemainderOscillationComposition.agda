module DASHI.Physics.Closure.NSCompactGammaRemainderOscillationComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Composition law for local integrated-remainder oscillation bounds.
--
-- A quadrature block is represented only by three already weighted scalars:
--
--   memberRemainder <= centerRemainder + allowance.
--
-- The theorem below shows that two independently controlled blocks compose to
-- one bound with summed center and allowance.  Iterating this theorem gives the
-- finite-time-grid estimate required by the compact-Gamma finite-net lane.
--
-- The analytic work still has to construct each local block from estimates on
-- (R - theta E)_+ and trajectory stability.  No numerical slope is promoted.
------------------------------------------------------------------------

record RemainderOscillationBound
    (A : AbsorptionArithmetic) : Set₁ where
  field
    centerRemainder : Scalar A
    memberRemainder : Scalar A
    oscillationAllowance : Scalar A

    memberNearCenter :
      _≤_ A memberRemainder
        (_+_ A centerRemainder oscillationAllowance)

open RemainderOscillationBound public

combineRemainderOscillationBounds :
  (A : AbsorptionArithmetic) →
  (left right : RemainderOscillationBound A) →
  RemainderOscillationBound A
combineRemainderOscillationBounds A left right = record
  { centerRemainder =
      _+_ A (centerRemainder left) (centerRemainder right)
  ; memberRemainder =
      _+_ A (memberRemainder left) (memberRemainder right)
  ; oscillationAllowance =
      _+_ A
        (oscillationAllowance left)
        (oscillationAllowance right)
  ; memberNearCenter = memberSum≤centerSumPlusAllowanceSum
  }
  where
  memberSum≤leftUpperPlusMemberRight :
    _≤_ A
      (_+_ A (memberRemainder left) (memberRemainder right))
      (_+_ A
        (_+_ A
          (centerRemainder left)
          (oscillationAllowance left))
        (memberRemainder right))
  memberSum≤leftUpperPlusMemberRight =
    additionMonotoneRight A (memberNearCenter left)

  leftUpperPlusMemberRight≤rawUpper :
    _≤_ A
      (_+_ A
        (_+_ A
          (centerRemainder left)
          (oscillationAllowance left))
        (memberRemainder right))
      (_+_ A
        (_+_ A
          (centerRemainder left)
          (oscillationAllowance left))
        (_+_ A
          (centerRemainder right)
          (oscillationAllowance right)))
  leftUpperPlusMemberRight≤rawUpper =
    additionMonotoneLeft A (memberNearCenter right)

  memberSum≤rawUpper :
    _≤_ A
      (_+_ A (memberRemainder left) (memberRemainder right))
      (_+_ A
        (_+_ A
          (centerRemainder left)
          (oscillationAllowance left))
        (_+_ A
          (centerRemainder right)
          (oscillationAllowance right)))
  memberSum≤rawUpper =
    ≤-trans A
      memberSum≤leftUpperPlusMemberRight
      leftUpperPlusMemberRight≤rawUpper

  middleInterchange :
    _+_ A
      (oscillationAllowance left)
      (_+_ A
        (centerRemainder right)
        (oscillationAllowance right))
    ≡
    _+_ A
      (centerRemainder right)
      (_+_ A
        (oscillationAllowance left)
        (oscillationAllowance right))
  middleInterchange =
    trans
      (sym
        (addAssociative A
          (oscillationAllowance left)
          (centerRemainder right)
          (oscillationAllowance right)))
      (trans
        (cong
          (λ middle → _+_ A middle (oscillationAllowance right))
          (addCommutative A
            (oscillationAllowance left)
            (centerRemainder right)))
        (addAssociative A
          (centerRemainder right)
          (oscillationAllowance left)
          (oscillationAllowance right)))

  rawUpperInterchange :
    _+_ A
      (_+_ A
        (centerRemainder left)
        (oscillationAllowance left))
      (_+_ A
        (centerRemainder right)
        (oscillationAllowance right))
    ≡
    _+_ A
      (_+_ A
        (centerRemainder left)
        (centerRemainder right))
      (_+_ A
        (oscillationAllowance left)
        (oscillationAllowance right))
  rawUpperInterchange =
    trans
      (addAssociative A
        (centerRemainder left)
        (oscillationAllowance left)
        (_+_ A
          (centerRemainder right)
          (oscillationAllowance right)))
      (trans
        (cong
          (λ tail → _+_ A (centerRemainder left) tail)
          middleInterchange)
        (sym
          (addAssociative A
            (centerRemainder left)
            (centerRemainder right)
            (_+_ A
              (oscillationAllowance left)
              (oscillationAllowance right)))))

  memberSum≤centerSumPlusAllowanceSum :
    _≤_ A
      (_+_ A (memberRemainder left) (memberRemainder right))
      (_+_ A
        (_+_ A
          (centerRemainder left)
          (centerRemainder right))
        (_+_ A
          (oscillationAllowance left)
          (oscillationAllowance right)))
  memberSum≤centerSumPlusAllowanceSum =
    subst
      (λ upper →
        _≤_ A
          (_+_ A (memberRemainder left) (memberRemainder right))
          upper)
      rawUpperInterchange
      memberSum≤rawUpper
