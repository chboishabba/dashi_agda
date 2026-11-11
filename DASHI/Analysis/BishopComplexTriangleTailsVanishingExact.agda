module DASHI.Analysis.BishopComplexTriangleTailsVanishingExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP FINITE POSITIVE CAUCHY TRIANGLE COMPARISON.
--
-- Comparison is proved via the existing Bishop Sequence.∑₀-mono-≤
-- and the already-proved FinSum.finSumIsSeriesOf bridge.
-- The complete original positive exponential triangle-tail convergence
-- is reused from BishopExponentialCauchyProductExact.
--
-- Unpaid: componentwise factorial-complex term majorization on all
-- indices, followed by domination of differences of positive prefixes.
-- No claim of a completed four-wing vanishing theorem is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (toℕ)
import Data.Nat.Base as ℕ

import Real as BishopReal
import RealProperties as BishopP
open import Data.Product.Base using (proj₁; proj₂)
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpCauchy
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as RealAxis
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisSignedTermsExact as Signed
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopEvenOddFullSequenceConvergenceExact as Parity
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Trig

originalBishopFiniteFinSumMonotone :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal._≤_ (left index) (right index)) →
  ∀ count →
  BishopReal._≤_
    (FinSum.finSum left count)
    (FinSum.finSum right count)
originalBishopFiniteFinSumMonotone
  {left} {right} pointwise count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (FinSum.finSumIsSeriesOf right count))
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm
        (FinSum.finSumIsSeriesOf left count))
      (BishopSequence.∑₀-mono-≤ pointwise count))

originalBishopCauchyCoefficientMonotone :
  ∀ {a b A B : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≤_ (a n) (A n)) →
  (∀ n → BishopReal._≤_ (b n) (B n)) →
  (∀ n → BishopReal.NonNegative (A n)) →
  (∀ n → BishopReal.NonNegative (b n)) →
  ∀ count →
  BishopReal._≤_
    (Row.cauchyCoefficient a b count)
    (Row.cauchyCoefficient A B count)
originalBishopCauchyCoefficientMonotone
  {a} {b} {A} {B} a≤A b≤B Ann bnn count =
  originalBishopFiniteFinSumMonotone
    (λ index →
      BishopP.≤-trans
        (BishopP.*-monoʳ-≤-nonNeg
          (a≤A index)
          (bnn (count ℕ.∸ index)))
        (BishopP.*-monoˡ-≤-nonNeg
          (b≤B (count ℕ.∸ index))
          (Ann index)))
    (suc count)

originalBishopCauchyTriangleMonotone :
  ∀ {a b A B : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≤_ (a n) (A n)) →
  (∀ n → BishopReal._≤_ (b n) (B n)) →
  (∀ n → BishopReal.NonNegative (A n)) →
  (∀ n → BishopReal.NonNegative (b n)) →
  ∀ count →
  BishopReal._≤_
    (Row.trianglePartial a b count)
    (Row.trianglePartial A B count)
originalBishopCauchyTriangleMonotone
  {a} {b} {A} {B} a≤A b≤B Ann bnn count =
  originalBishopFiniteFinSumMonotone
    (originalBishopCauchyCoefficientMonotone
      a≤A b≤B Ann bnn)
    count

-- This convergence is not a newly proposed witness. It is the
-- pinned Bishop real factorial exponential triangle-tail theorem.
originalBishopFactorialPositiveTriangleTailVanishes :
  ∀ x y →
  BishopSequence._ConvergesTo_
    (ExpCauchy.absoluteTriangleWingTail x y)
    BishopReal.0ℝ
originalBishopFactorialPositiveTriangleTailVanishes =
  ExpCauchy.absoluteTriangleWingTailConvergesZero


------------------------------------------------------------------------
-- LITERAL REAL-AXIS FACTOR OF THE COMPLEX EXPONENTIAL PRODUCT.
-- Its absolute coefficient is exactly the pinned real factorial
-- exponential absolute coefficient. Its imaginary coefficient is
-- identically zero, with the proof from the original all-degree
-- factorial complex source.
------------------------------------------------------------------------

originalBishopRealFactorAbsoluteIsExpAbsolute :
  ∀ x n →
  BishopReal._≃_
    (BishopReal.∣ Complex.re
      (RealAxis.originalBishopFactorialComplexTerm
        (RealAxis.realAxis x) n) ∣)
    (ExpCauchy.absoluteExpTerm x n)
originalBishopRealFactorAbsoluteIsExpAbsolute x n =
  BishopP.∣-∣-cong
    (proj₁ (RealAxis.originalBishopFactorialComplexTermRealAxis x n))

originalBishopRealFactorImaginaryZero :
  ∀ x n →
  BishopReal._≃_
    (Complex.im
      (RealAxis.originalBishopFactorialComplexTerm
        (RealAxis.realAxis x) n))
    BishopReal.0ℝ
originalBishopRealFactorImaginaryZero x n =
  proj₂ (RealAxis.originalBishopFactorialComplexTermRealAxis x n)


------------------------------------------------------------------------
-- IMAGINARY AXIS: SAME-SOURCE ALL-DEGREE ABSOLUTE FACTORIAL
-- MAJORANT. Reuses original parity power identities, not an axiom.
------------------------------------------------------------------------

originalBishopSignedFactorialAbsIsMagnitude :
  (y : BishopReal.ℝ) (index degree : Nat) →
  BishopReal._≃_
    (BishopReal.∣ BishopReal._*_
      (Trig.alternatingSign index)
      (BishopReal._*_
        (Exp.embed (Exp.inverseFactorial degree))
        (BishopReal.pow y degree)) ∣)
    (Exp.expMagnitudeTerm y degree)
originalBishopSignedFactorialAbsIsMagnitude y index degree =
  let
    sign = Trig.alternatingSign index
    coeff = Exp.embed (Exp.inverseFactorial degree)
    power = BishopReal.pow y degree
  in
  BishopP.≃-trans
    (BishopP.∣x*y∣≃∣x∣*∣y∣ sign
      (BishopReal._*_ coeff power))
    (BishopP.≃-trans
      (BishopP.*-cong
        (Machin.alternatingSignAbsOne index)
        (BishopP.≃-trans
          (BishopP.∣x*y∣≃∣x∣*∣y∣ coeff power)
          (BishopP.*-congʳ
            (BishopP.0≤x⇒∣x∣≃x
              (BishopP.nonNegx⇒0≤x
                (Exp.embeddedInverseFactorialNonnegative degree))))))
      (BishopP.*-identityˡ
        (Exp.expMagnitudeTerm y degree)))

originalBishopImaginaryEvenRealAbsIsExpAbs :
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∣ Complex.re
      (RealAxis.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y)
        (Estimates.evenExponent n)) ∣)
    (ExpCauchy.absoluteExpTerm y (Estimates.evenExponent n))
originalBishopImaginaryEvenRealAbsIsExpAbs y n =
  BishopP.≃-trans
    (BishopP.∣-∣-cong
      (Signed.originalBishopImaginaryAxisCosineSignedTerm y n))
    (BishopP.≃-trans
      (originalBishopSignedFactorialAbsIsMagnitude
        y n (Estimates.evenExponent n))
      (BishopP.≃-symm
        (Exp.expTermAbsIsMagnitude
          y (Estimates.evenExponent n))))

originalBishopImaginaryOddImagAbsIsExpAbs :
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∣ Complex.im
      (RealAxis.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y)
        (Estimates.oddExponent n)) ∣)
    (ExpCauchy.absoluteExpTerm y (Estimates.oddExponent n))
originalBishopImaginaryOddImagAbsIsExpAbs y n =
  BishopP.≃-trans
    (BishopP.∣-∣-cong
      (Signed.originalBishopImaginaryAxisSineSignedTerm y n))
    (BishopP.≃-trans
      (originalBishopSignedFactorialAbsIsMagnitude
        y n (Estimates.oddExponent n))
      (BishopP.≃-symm
        (Exp.expTermAbsIsMagnitude
          y (Estimates.oddExponent n))))

originalBishopImaginaryRealAbsBound :
  ∀ y n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re
      (RealAxis.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) n) ∣)
    (ExpCauchy.absoluteExpTerm y n)
originalBishopImaginaryRealAbsBound y n
  with Parity.parityCover n
... | Parity.even j =
  BishopP.≤-reflexive
    (originalBishopImaginaryEvenRealAbsIsExpAbs y j)
... | Parity.odd j =
  BishopP.≤-respˡ-≃
    (BishopP.∣-∣-cong
      (proj₁ (Axis.originalBishopImaginaryAxisFactorialOddTerm y j)))
    (BishopP.nonNegx⇒0≤x
      (BishopP.nonNeg∣x∣
        (Exp.expTerm y (Estimates.oddExponent j))))

originalBishopImaginaryImagAbsBound :
  ∀ y n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im
      (RealAxis.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) n) ∣)
    (ExpCauchy.absoluteExpTerm y n)
originalBishopImaginaryImagAbsBound y n
  with Parity.parityCover n
... | Parity.odd j =
  BishopP.≤-reflexive
    (originalBishopImaginaryOddImagAbsIsExpAbs y j)
... | Parity.even j =
  BishopP.≤-respˡ-≃
    (BishopP.∣-∣-cong
      (proj₂ (Axis.originalBishopImaginaryAxisFactorialEvenTerm y j)))
    (BishopP.nonNegx⇒0≤x
      (BishopP.nonNeg∣x∣
        (Exp.expTerm y (Estimates.evenExponent j))))
