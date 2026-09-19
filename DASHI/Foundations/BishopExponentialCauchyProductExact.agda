module DASHI.Foundations.BishopExponentialCauchyProductExact where

------------------------------------------------------------------------
-- CONCRETE BISHOP EXPONENTIAL: CAUCHY PRODUCT / ADDITIVITY
--
-- DASHI CONTRIBUTION
--
-- The finite layer already owns:
--
--   * exact exponential Cauchy coefficients;
--   * rectangle = product of finite partial sums;
--   * Cauchy triangle reindexing;
--   * the absolute finite wing estimate
--
--       |R_N - T_N| <= T^+_(2N) - T^+_N.
--
-- Absolute exponential convergence makes the positive right-hand tail vanish.
-- Therefore the rectangle and Cauchy triangle have the same limit.  The
-- rectangle limit is exp(x)exp(y), while the coefficient identity identifies
-- the triangle limit with exp(x+y).
--
-- No abstract CauchyProductAuthority, Mertens postulate, or external analytic
-- theorem is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (toℕ)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as TriangleExp
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle

module BishopSum = SemiringSum BishopP.+-*-semiring

absoluteExpTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
absoluteExpTerm value index =
  BishopReal.∣ Exp.expTerm value index ∣

absoluteExpTermIsExpAbs :
  ∀ value index →
  BishopReal._≃_
    (absoluteExpTerm value index)
    (Exp.expTerm (BishopReal.∣ value ∣) index)
absoluteExpTermIsExpAbs value index =
  BishopP.≃-trans
    (Exp.expTermAbsIsMagnitude value index)
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (BishopSequence.∣xⁿ∣≃∣x∣ⁿ value index))
      (BishopP.*-comm
        (Exp.embed (Exp.inverseFactorial index))
        (BishopReal.pow (BishopReal.∣ value ∣) index)))

cauchyCoefficientAbsoluteExpCongruent :
  ∀ left right total →
  BishopReal._≃_
    (Row.cauchyCoefficient
      (absoluteExpTerm left)
      (absoluteExpTerm right)
      total)
    (Row.cauchyCoefficient
      (Exp.expTerm (BishopReal.∣ left ∣))
      (Exp.expTerm (BishopReal.∣ right ∣))
      total)
cauchyCoefficientAbsoluteExpCongruent left right total =
  BishopSum.sum-cong-≋
    (λ index →
      BishopP.*-cong
        (absoluteExpTermIsExpAbs left (toℕ index))
        (absoluteExpTermIsExpAbs
          right
          (total Nat.∸ toℕ index)))

absoluteTriangle :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
absoluteTriangle left right count =
  Row.trianglePartial
    (absoluteExpTerm left)
    (absoluteExpTerm right)
    count

absoluteTriangleIsExpAbsPartial :
  ∀ left right count →
  BishopReal._≃_
    (absoluteTriangle left right count)
    (BishopSequence.SeriesOf
      (Exp.expTerm
        (BishopReal._+_
          (BishopReal.∣ left ∣)
          (BishopReal.∣ right ∣)))
      count)
absoluteTriangleIsExpAbsPartial left right count =
  BishopP.≃-trans
    (BishopSum.sum-cong-≋
      (λ index →
        cauchyCoefficientAbsoluteExpCongruent
          left right (toℕ index)))
    (TriangleExp.expTriangleIsPartialSum
      (BishopReal.∣ left ∣)
      (BishopReal.∣ right ∣)
      count)

absoluteTriangleConverges :
  ∀ left right →
  BishopSequence._ConvergesTo_
    (absoluteTriangle left right)
    (Exp.bishopExp
      (BishopReal._+_
        (BishopReal.∣ left ∣)
        (BishopReal.∣ right ∣)))
absoluteTriangleConverges left right =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (absoluteTriangleIsExpAbsPartial
          left right (suc count-1))})
    ( Exp.bishopExp
        (BishopReal._+_
          (BishopReal.∣ left ∣)
          (BishopReal.∣ right ∣))
    , Exp.bishopExpConverges
        (BishopReal._+_
          (BishopReal.∣ left ∣)
          (BishopReal.∣ right ∣))
    )

doubleIsAddSelf : ∀ count → Double.double count ≡ count + count
doubleIsAddSelf zero = refl
doubleIsAddSelf (suc count) =
  cong suc
    (trans
      (cong suc (doubleIsAddSelf count))
      (sym (NatP.+-suc count count)))

absoluteTriangleWingTail :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
absoluteTriangleWingTail left right count =
  BishopReal._-_
    (absoluteTriangle left right (count + count))
    (absoluteTriangle left right count)

absoluteTriangleDoubleTail :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
absoluteTriangleDoubleTail left right count =
  BishopReal._-_
    (absoluteTriangle left right (Double.double count))
    (absoluteTriangle left right count)

absoluteTriangleWingTailEquivalentDoubleTail :
  ∀ left right count →
  BishopReal._≃_
    (absoluteTriangleDoubleTail left right count)
    (absoluteTriangleWingTail left right count)
absoluteTriangleWingTailEquivalentDoubleTail left right count =
  BishopP.+-cong
    (BishopP.≃-refl₂
      (cong
        (absoluteTriangle left right)
        (doubleIsAddSelf count)))
    BishopP.≃-refl

absoluteTriangleWingTailConvergesZero :
  ∀ left right →
  BishopSequence._ConvergesTo_
    (absoluteTriangleWingTail left right)
    BishopReal.0ℝ
absoluteTriangleWingTailConvergesZero left right =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      absoluteTriangleWingTailEquivalentDoubleTail
        left right (suc count-1)})
    ( BishopReal.0ℝ
    , Double.doubleTailConvergesZero
        (absoluteTriangleConverges left right)
    )

rectanglePartial :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
rectanglePartial left right count =
  Rectangle.rectangleSum
    (Exp.expTerm left)
    (Exp.expTerm right)
    count count

trianglePartial :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
trianglePartial left right count =
  Row.trianglePartial
    (Exp.expTerm left)
    (Exp.expTerm right)
    count

productPartial :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
productPartial left right count =
  BishopReal._*_
    (BishopSequence.SeriesOf (Exp.expTerm left) count)
    (BishopSequence.SeriesOf (Exp.expTerm right) count)

rectangleConvergesToProduct :
  ∀ left right →
  BishopSequence._ConvergesTo_
    (rectanglePartial left right)
    (BishopReal._*_
      (Exp.bishopExp left)
      (Exp.bishopExp right))
rectangleConvergesToProduct left right =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (Rectangle.rectangleProduct
          (Exp.expTerm left)
          (Exp.expTerm right)
          (suc count-1)
          (suc count-1))})
    ( BishopReal._*_
        (Exp.bishopExp left)
        (Exp.bishopExp right)
    , BishopSequence.xₙyₙ→x₀y₀
        (Exp.bishopExp left , Exp.bishopExpConverges left)
        (Exp.bishopExp right , Exp.bishopExpConverges right)
    )

triangleConvergesToExpAdd :
  ∀ left right →
  BishopSequence._ConvergesTo_
    (trianglePartial left right)
    (Exp.bishopExp (BishopReal._+_ left right))
triangleConvergesToExpAdd left right =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (TriangleExp.expTriangleIsPartialSum
          left right (suc count-1))})
    ( Exp.bishopExp (BishopReal._+_ left right)
    , Exp.bishopExpConverges
        (BishopReal._+_ left right)
    )

finiteWingBoundByAbsoluteVanishingTail :
  ∀ left right count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (rectanglePartial left right count)
        (trianglePartial left right count)
    ∣)
    (BishopReal.∣
      absoluteTriangleWingTail left right count
    ∣)
finiteWingBoundByAbsoluteVanishingTail left right count =
  BishopP.≤-trans
    (Wing.finiteCauchyWingAbsoluteBound
      (Exp.expTerm left)
      (Exp.expTerm right)
      count)
    (BishopP.x≤∣x∣
      {x = absoluteTriangleWingTail left right count})

rectangleConvergesToExpAdd :
  ∀ left right →
  BishopSequence._ConvergesTo_
    (rectanglePartial left right)
    (Exp.bishopExp (BishopReal._+_ left right))
rectangleConvergesToExpAdd left right =
  Vanish.vanishingDifferenceConvergence
    (triangleConvergesToExpAdd left right)
    (absoluteTriangleWingTailConvergesZero left right)
    (finiteWingBoundByAbsoluteVanishingTail left right)

bishopExpAdd :
  ∀ left right →
  BishopReal._≃_
    (Exp.bishopExp (BishopReal._+_ left right))
    (BishopReal._*_
      (Exp.bishopExp left)
      (Exp.bishopExp right))
bishopExpAdd left right =
  BishopP.≃-symm
    (BishopSequence.uniqueness-of-limits
      (rectangleConvergesToProduct left right)
      (rectangleConvergesToExpAdd left right))

bishopExpTimesNegativeIsOne :
  ∀ value →
  BishopReal._≃_
    (BishopReal._*_
      (Exp.bishopExp value)
      (Exp.bishopExp (BishopReal.- value)))
    BishopReal.1ℝ
bishopExpTimesNegativeIsOne value =
  BishopP.≃-trans
    (BishopP.≃-symm
      (bishopExpAdd value (BishopReal.- value)))
    (BishopP.≃-trans
      (ExpCong.bishopExpCongruent
        (BishopP.+-inverseʳ value))
      Positive.bishopExpZero)
