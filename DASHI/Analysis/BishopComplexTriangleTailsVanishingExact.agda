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

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Fin.Base using (toℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as NatP

import Real as BishopReal
import RealProperties as BishopP
open import Data.Product.Base using (proj₁; proj₂)
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpCauchy
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as RealAxis
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as ComplexWing
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


------------------------------------------------------------------------
-- TAIL ORDER IS A SEPARATE THEOREM: prefix monotonicity alone
-- does not imply that differences of prefixes preserve order.
-- The vendored Bishop finite-interval ∑-mono-≤ pays precisely this.
------------------------------------------------------------------------

originalBishopTriangleTailIsInterval :
  (a b : Nat → BishopReal.ℝ) →
  ∀ start count →
  BishopReal._≃_
    (BishopReal._-_
      (Row.trianglePartial a b (start + count))
      (Row.trianglePartial a b start))
    (BishopSequence.∑ (Row.cauchyCoefficient a b)
      start (start + count))
originalBishopTriangleTailIsInterval a b start count =
  let
    coefficient = Row.cauchyCoefficient a b
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (FinSum.finSumIsSeriesOf coefficient (start + count))
      (BishopP.-‿cong (FinSum.finSumIsSeriesOf coefficient start)))
    (BishopP.≃-symm
      (BishopSequence.∑ₙᵐ≃∑₀ᵐ-∑₀ⁿ
        coefficient start (start + count)))

originalBishopCauchyTriangleTailMonotone :
  ∀ {a b A B : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≤_ (a n) (A n)) →
  (∀ n → BishopReal._≤_ (b n) (B n)) →
  (∀ n → BishopReal.NonNegative (A n)) →
  (∀ n → BishopReal.NonNegative (b n)) →
  ∀ start count →
  BishopReal._≤_
    (BishopReal._-_
      (Row.trianglePartial a b (start + count))
      (Row.trianglePartial a b start))
    (BishopReal._-_
      (Row.trianglePartial A B (start + count))
      (Row.trianglePartial A B start))
originalBishopCauchyTriangleTailMonotone
  {a} {b} {A} {B} a≤A b≤B Ann bnn start count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (originalBishopTriangleTailIsInterval A B start count))
    (BishopP.≤-respˡ-≃
      (originalBishopTriangleTailIsInterval a b start count)
      (BishopSequence.∑-mono-≤
        (originalBishopCauchyCoefficientMonotone
          a≤A b≤B Ann bnn)
        start (start + count)
        (NatP.m≤m+n start count)))


------------------------------------------------------------------------
-- INSTANTIATED FOUR ORIGINAL COMPLEX FACTORIAL POSITIVE WINGS.
-- The source pairing is the actual exp-factorial (x,0) with
-- exp-factorial (0,y), with no abstract comparison record.
------------------------------------------------------------------------

factorialRealStream :
  BishopReal.ℝ → Nat → Complex.BishopComplex
factorialRealStream x n =
  RealAxis.originalBishopFactorialComplexTerm (RealAxis.realAxis x) n

factorialImaginaryStream :
  BishopReal.ℝ → Nat → Complex.BishopComplex
factorialImaginaryStream y n =
  RealAxis.originalBishopFactorialComplexTerm (Axis.imaginaryAxis y) n

doubleAbsolute :
  ∀ value →
  BishopReal._≃_
    (BishopReal.∣ BishopReal.∣ value ∣ ∣)
    (BishopReal.∣ value ∣)
doubleAbsolute value =
  BishopP.0≤x⇒∣x∣≃x
    (BishopP.nonNegx⇒0≤x (BishopP.nonNeg∣x∣ value))

realFactorRealAbsoluteBound :
  ∀ x n →
  BishopReal._≤_
    (Wing.absoluteTerms (Complex.realTerms (factorialRealStream x)) n)
    (ExpCauchy.absoluteExpTerm x n)
realFactorRealAbsoluteBound x n =
  BishopP.≤-reflexive
    (originalBishopRealFactorAbsoluteIsExpAbsolute x n)

realFactorImagAbsoluteBound :
  ∀ x n →
  BishopReal._≤_
    (Wing.absoluteTerms (Complex.imagTerms (factorialRealStream x)) n)
    (ExpCauchy.absoluteExpTerm x n)
realFactorImagAbsoluteBound x n =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      (BishopP.∣-∣-cong
        (originalBishopRealFactorImaginaryZero x n))
      (BishopP.0≤x⇒∣x∣≃x BishopP.≤-refl))
    (BishopP.nonNegx⇒0≤x
      (BishopP.nonNeg∣x∣ (Exp.expTerm x n)))

imaginaryFactorRealAbsoluteBound :
  ∀ y n →
  BishopReal._≤_
    (Wing.absoluteTerms (Complex.realTerms (factorialImaginaryStream y)) n)
    (ExpCauchy.absoluteExpTerm y n)
imaginaryFactorRealAbsoluteBound =
  originalBishopImaginaryRealAbsBound

imaginaryFactorImagAbsoluteBound :
  ∀ y n →
  BishopReal._≤_
    (Wing.absoluteTerms (Complex.imagTerms (factorialImaginaryStream y)) n)
    (ExpCauchy.absoluteExpTerm y n)
imaginaryFactorImagAbsoluteBound =
  originalBishopImaginaryImagAbsBound

originalBishopFourFactorialPositiveTailBound :
  ∀ x y count →
  BishopReal._≤_
    (BishopReal._+_
      (ComplexWing.positiveTriangleTail
        (Complex.realTerms (factorialRealStream x))
        (Complex.realTerms (factorialImaginaryStream y))
        count)
      (ComplexWing.positiveTriangleTail
        (Complex.imagTerms (factorialRealStream x))
        (Complex.imagTerms (factorialImaginaryStream y))
        count))
    (BishopReal._+_
      (ExpCauchy.absoluteTriangleWingTail x y)
      (ExpCauchy.absoluteTriangleWingTail x y))
originalBishopFourFactorialPositiveTailBound x y count =
  let
    A = ExpCauchy.absoluteExpTerm x
    B = ExpCauchy.absoluteExpTerm y
    Ann : ∀ n → BishopReal.NonNegative (A n)
    Ann n = BishopP.nonNeg∣x∣ (Exp.expTerm x n)
    realBnn : ∀ n →
      BishopReal.NonNegative
        (Wing.absoluteTerms
          (Complex.realTerms (factorialImaginaryStream y)) n)
    realBnn n = BishopP.nonNeg∣x∣
      (Complex.realTerms (factorialImaginaryStream y) n)
    imagBnn : ∀ n →
      BishopReal.NonNegative
        (Wing.absoluteTerms
          (Complex.imagTerms (factorialImaginaryStream y)) n)
    imagBnn n = BishopP.nonNeg∣x∣
      (Complex.imagTerms (factorialImaginaryStream y) n)
  in
  BishopP.+-mono-≤
    (originalBishopCauchyTriangleTailMonotone
      (realFactorRealAbsoluteBound x)
      (imaginaryFactorRealAbsoluteBound y)
      Ann realBnn count count)
    (originalBishopCauchyTriangleTailMonotone
      (realFactorImagAbsoluteBound x)
      (imaginaryFactorImagAbsoluteBound y)
      Ann imagBnn count count)

originalBishopFourFactorialImaginaryTailBound :
  ∀ x y count →
  BishopReal._≤_
    (BishopReal._+_
      (ComplexWing.positiveTriangleTail
        (Complex.realTerms (factorialRealStream x))
        (Complex.imagTerms (factorialImaginaryStream y))
        count)
      (ComplexWing.positiveTriangleTail
        (Complex.imagTerms (factorialRealStream x))
        (Complex.realTerms (factorialImaginaryStream y))
        count))
    (BishopReal._+_
      (ExpCauchy.absoluteTriangleWingTail x y)
      (ExpCauchy.absoluteTriangleWingTail x y))
originalBishopFourFactorialImaginaryTailBound x y count =
  let
    A = ExpCauchy.absoluteExpTerm x
    Ann : ∀ n → BishopReal.NonNegative (A n)
    Ann n = BishopP.nonNeg∣x∣ (Exp.expTerm x n)
    realBnn : ∀ n →
      BishopReal.NonNegative
        (Wing.absoluteTerms
          (Complex.realTerms (factorialImaginaryStream y)) n)
    realBnn n = BishopP.nonNeg∣x∣
      (Complex.realTerms (factorialImaginaryStream y) n)
    imagBnn : ∀ n →
      BishopReal.NonNegative
        (Wing.absoluteTerms
          (Complex.imagTerms (factorialImaginaryStream y)) n)
    imagBnn n = BishopP.nonNeg∣x∣
      (Complex.imagTerms (factorialImaginaryStream y) n)
  in
  BishopP.+-mono-≤
    (originalBishopCauchyTriangleTailMonotone
      (realFactorRealAbsoluteBound x)
      (imaginaryFactorImagAbsoluteBound y)
      Ann imagBnn count count)
    (originalBishopCauchyTriangleTailMonotone
      (realFactorImagAbsoluteBound x)
      (imaginaryFactorRealAbsoluteBound y)
      Ann realBnn count count)
