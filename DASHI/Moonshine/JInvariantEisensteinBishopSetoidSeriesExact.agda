module DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact where

------------------------------------------------------------------------
-- SETOID-NATIVE BISHOP E4/E6 q-SERIES
--
-- DASHI CONTRIBUTION
--
-- This owner constructs the Eisenstein q-series directly on the concrete
-- Murray/Bishop real carrier.  It deliberately does NOT pass through the
-- older propositional-equality ConstructedOrderedCompleteReal/ConcreteComplex
-- package.
--
-- The q-specific analytic input is reduced to one componentwise power
-- envelope:
--
--   |Re(q^(n+1))| <= r^(n+1)
--   |Im(q^(n+1))| <= r^(n+1)
--
-- for a Bishop radius 0 <= r < 1.
--
-- Existing finite divisor arithmetic supplies the exact coefficients and
-- polynomial envelopes; the already-owned Bishop polynomial/geometric theorem
-- supplies the convergent majorants.  Bishop's comparison test then gives
-- componentwise absolute convergence of the literal E4/E6 tails.
--
-- This proves existence of constructive Bishop E4/E6 q-series objects once a
-- q object with the stated component envelope is supplied.  It does NOT yet
-- identify those limits with lattice Eisenstein series, nor with the older
-- legacy ConcreteComplex evaluator.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PolyGeo
open import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact public using (BishopQPowerComponentEnvelope; realPowerBound; imagPowerBound)
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as NatMono
import DASHI.Foundations.BishopNatEmbeddingPowerExact as NatPower
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as Coeff
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Majorant

------------------------------------------------------------------------
-- Literal Bishop E4/E6 tail terms.
------------------------------------------------------------------------

e4CoefficientReal : Nat → BishopReal.ℝ
e4CoefficientReal n =
  NatReal.natReal (Coeff.e4IncrementCoefficient n)

e6CoefficientReal : Nat → BishopReal.ℝ
e6CoefficientReal n =
  NatReal.natReal (Coeff.e6IncrementCoefficient n)

e4BishopTerm : Complex.BishopComplex → Nat → Complex.BishopComplex
e4BishopTerm q n =
  Algebra.scaleC
    (e4CoefficientReal n)
    (Algebra.powC q (suc n))

e6BishopUnsignedTerm : Complex.BishopComplex → Nat → Complex.BishopComplex
e6BishopUnsignedTerm q n =
  Algebra.scaleC
    (e6CoefficientReal n)
    (Algebra.powC q (suc n))

------------------------------------------------------------------------
-- Exact coefficient envelopes after the canonical Nat -> Bishop embedding.
------------------------------------------------------------------------

e4CoefficientUpper : Nat → BishopReal.ℝ
e4CoefficientUpper n =
  BishopReal._*_
    Majorant.e4Scale
    (BishopReal.pow (NatReal.natReal (suc n)) 4)

e6CoefficientUpper : Nat → BishopReal.ℝ
e6CoefficientUpper n =
  BishopReal._*_
    Majorant.e6Scale
    (BishopReal.pow (NatReal.natReal (suc n)) 6)

e4CoefficientUpperMeaning :
  ∀ n →
  BishopReal._≃_
    (NatReal.natReal
      (240 * (Divisor.powNat (suc n) 3 * suc n)))
    (e4CoefficientUpper n)
e4CoefficientUpperMeaning n =
  BishopP.≃-trans
    (NatReal.natRealMul
      240
      (Divisor.powNat (suc n) 3 * suc n))
    (BishopP.*-congˡ
      (NatPower.natRealPowNatTimesBase (suc n) 3))

e6CoefficientUpperMeaning :
  ∀ n →
  BishopReal._≃_
    (NatReal.natReal
      (504 * (Divisor.powNat (suc n) 5 * suc n)))
    (e6CoefficientUpper n)
e6CoefficientUpperMeaning n =
  BishopP.≃-trans
    (NatReal.natRealMul
      504
      (Divisor.powNat (suc n) 5 * suc n))
    (BishopP.*-congˡ
      (NatPower.natRealPowNatTimesBase (suc n) 5))

e4CoefficientBound :
  ∀ n →
  BishopReal._≤_
    (e4CoefficientReal n)
    (e4CoefficientUpper n)
e4CoefficientBound n =
  BishopP.≤-respʳ-≃
    (e4CoefficientUpperMeaning n)
    (NatMono.natRealMonotone
      (Coeff.e4IncrementCoefficientBound n))

e6CoefficientBound :
  ∀ n →
  BishopReal._≤_
    (e6CoefficientReal n)
    (e6CoefficientUpper n)
e6CoefficientBound n =
  BishopP.≤-respʳ-≃
    (e6CoefficientUpperMeaning n)
    (NatMono.natRealMonotone
      (Coeff.e6IncrementCoefficientBound n))

e4CoefficientNonnegative : ∀ n → BishopReal.NonNegative (e4CoefficientReal n)
e4CoefficientNonnegative n =
  PolyGeo.natRealNonnegative (Coeff.e4IncrementCoefficient n)

e6CoefficientNonnegative : ∀ n → BishopReal.NonNegative (e6CoefficientReal n)
e6CoefficientNonnegative n =
  PolyGeo.natRealNonnegative (Coeff.e6IncrementCoefficient n)

------------------------------------------------------------------------
-- q power component envelope.
------------------------------------------------------------------------

ratioPowerNonnegative :
  ∀ {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  ∀ n →
  BishopReal.NonNegative (BishopReal.pow ratio n)
ratioPowerNonnegative unit n =
  BishopSequence.nonNegx⇒nonNegxⁿ n
    (BishopP.0≤x⇒nonNegx (Unit.ratioNonnegative unit))

------------------------------------------------------------------------
-- Canonical majorant normal forms.
------------------------------------------------------------------------

e4MajorantMeaning :
  ∀ ratio n →
  BishopReal._≃_
    (BishopReal._*_
      (e4CoefficientUpper n)
      (BishopReal.pow ratio (suc n)))
    (Majorant.e4MajorantTerm ratio n)
e4MajorantMeaning ratio n =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ scale polynomial geometric →
      (scale ⊗ polynomial) ⊗ geometric
      ⊜ scale ⊗ (polynomial ⊗ geometric))
    BishopP.≃-refl
    Majorant.e4Scale
    (BishopReal.pow (NatReal.natReal (suc n)) 4)
    (BishopReal.pow ratio (suc n))

e6MajorantMeaning :
  ∀ ratio n →
  BishopReal._≃_
    (BishopReal._*_
      (e6CoefficientUpper n)
      (BishopReal.pow ratio (suc n)))
    (Majorant.e6MajorantTerm ratio n)
e6MajorantMeaning ratio n =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ scale polynomial geometric →
      (scale ⊗ polynomial) ⊗ geometric
      ⊜ scale ⊗ (polynomial ⊗ geometric))
    BishopP.≃-refl
    Majorant.e6Scale
    (BishopReal.pow (NatReal.natReal (suc n)) 6)
    (BishopReal.pow ratio (suc n))

------------------------------------------------------------------------
-- Componentwise term bounds.
------------------------------------------------------------------------

scaledComponentAbsoluteBound :
  ∀ {coefficient coefficientUpper component componentUpper} →
  BishopReal.NonNegative coefficient →
  BishopReal.NonNegative componentUpper →
  BishopReal._≤_ coefficient coefficientUpper →
  BishopReal._≤_ (BishopReal.∣ component ∣) componentUpper →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._*_ coefficient component ∣)
    (BishopReal._*_ coefficientUpper componentUpper)
scaledComponentAbsoluteBound
    coefficientNN upperNN coefficientBound componentBound =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      (BishopP.∣x*y∣≃∣x∣*∣y∣ _ _)
      (BishopP.*-congʳ
        (BishopP.nonNegx⇒∣x∣≃x coefficientNN)))
    (BishopP.*-mono-≤
      coefficientNN
      (BishopP.nonNeg∣x∣ _)
      coefficientBound
      componentBound)

e4RealTermBound :
  ∀ q {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re (e4BishopTerm q n) ∣)
    (Majorant.e4MajorantTerm ratio n)
e4RealTermBound q {ratio} unit envelope n =
  BishopP.≤-respʳ-≃
    (e4MajorantMeaning ratio n)
    (scaledComponentAbsoluteBound
      (e4CoefficientNonnegative n)
      (ratioPowerNonnegative unit (suc n))
      (e4CoefficientBound n)
      (realPowerBound envelope n))

e4ImagTermBound :
  ∀ q {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im (e4BishopTerm q n) ∣)
    (Majorant.e4MajorantTerm ratio n)
e4ImagTermBound q {ratio} unit envelope n =
  BishopP.≤-respʳ-≃
    (e4MajorantMeaning ratio n)
    (scaledComponentAbsoluteBound
      (e4CoefficientNonnegative n)
      (ratioPowerNonnegative unit (suc n))
      (e4CoefficientBound n)
      (imagPowerBound envelope n))

e6RealTermBound :
  ∀ q {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re (e6BishopUnsignedTerm q n) ∣)
    (Majorant.e6MajorantTerm ratio n)
e6RealTermBound q {ratio} unit envelope n =
  BishopP.≤-respʳ-≃
    (e6MajorantMeaning ratio n)
    (scaledComponentAbsoluteBound
      (e6CoefficientNonnegative n)
      (ratioPowerNonnegative unit (suc n))
      (e6CoefficientBound n)
      (realPowerBound envelope n))

e6ImagTermBound :
  ∀ q {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im (e6BishopUnsignedTerm q n) ∣)
    (Majorant.e6MajorantTerm ratio n)
e6ImagTermBound q {ratio} unit envelope n =
  BishopP.≤-respʳ-≃
    (e6MajorantMeaning ratio n)
    (scaledComponentAbsoluteBound
      (e6CoefficientNonnegative n)
      (ratioPowerNonnegative unit (suc n))
      (e6CoefficientBound n)
      (imagPowerBound envelope n))

------------------------------------------------------------------------
-- Comparison with the already-owned scalar majorants.
------------------------------------------------------------------------

absoluteSeriesFromMajorant :
  (terms majorant : Nat → BishopReal.ℝ) →
  BishopSequence.SeriesOf_ConvergesAbsolutely majorant →
  (∀ n → BishopReal._≤_ (BishopReal.∣ terms n ∣) (majorant n)) →
  BishopSequence.SeriesOf_ConvergesAbsolutely terms
absoluteSeriesFromMajorant terms majorant majorantAbsolute bound =
  BishopSequence.proposition-3-5
    (BishopSequence.absolute⇒isConvergent majorantAbsolute)
    (zero , λ n _ →
      BishopP.≤-respˡ-≃
        (BishopP.nonNegx⇒∣x∣≃x
          (BishopP.nonNeg∣x∣ (terms n)))
        (bound n))

e4BishopComponentwiseAbsoluteConvergence :
  ∀ (q : Complex.BishopComplex) {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (e4BishopTerm q)
e4BishopComponentwiseAbsoluteConvergence q {ratio} unit envelope =
  Complex.componentwise-absolute-series-convergent
    (absoluteSeriesFromMajorant
      (Complex.realTerms (e4BishopTerm q))
      (Majorant.e4MajorantTerm ratio)
      (Majorant.e4MajorantAbsoluteConvergence unit)
      (e4RealTermBound q unit envelope))
    (absoluteSeriesFromMajorant
      (Complex.imagTerms (e4BishopTerm q))
      (Majorant.e4MajorantTerm ratio)
      (Majorant.e4MajorantAbsoluteConvergence unit)
      (e4ImagTermBound q unit envelope))

e6BishopComponentwiseAbsoluteConvergence :
  ∀ (q : Complex.BishopComplex) {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopQPowerComponentEnvelope q ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (e6BishopUnsignedTerm q)
e6BishopComponentwiseAbsoluteConvergence q {ratio} unit envelope =
  Complex.componentwise-absolute-series-convergent
    (absoluteSeriesFromMajorant
      (Complex.realTerms (e6BishopUnsignedTerm q))
      (Majorant.e6MajorantTerm ratio)
      (Majorant.e6MajorantAbsoluteConvergence unit)
      (e6RealTermBound q unit envelope))
    (absoluteSeriesFromMajorant
      (Complex.imagTerms (e6BishopUnsignedTerm q))
      (Majorant.e6MajorantTerm ratio)
      (Majorant.e6MajorantAbsoluteConvergence unit)
      (e6ImagTermBound q unit envelope))

------------------------------------------------------------------------
-- Canonical Bishop E4/E6 q-series values.
------------------------------------------------------------------------

e4BishopTailLimit :
  ∀ (q : Complex.BishopComplex) {ratio} →
  (unit : Unit.BishopUnitIntervalRatio ratio) →
  (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e4BishopTailLimit q unit envelope =
  Complex.complexSeriesLimit
    (e4BishopTerm q)
    (e4BishopComponentwiseAbsoluteConvergence q unit envelope)

e6BishopUnsignedTailLimit :
  ∀ (q : Complex.BishopComplex) {ratio} →
  (unit : Unit.BishopUnitIntervalRatio ratio) →
  (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e6BishopUnsignedTailLimit q unit envelope =
  Complex.complexSeriesLimit
    (e6BishopUnsignedTerm q)
    (e6BishopComponentwiseAbsoluteConvergence q unit envelope)

e4BishopTailConvergence :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.ComplexSeriesConvergesTo
    (e4BishopTerm q)
    (e4BishopTailLimit q unit envelope)
e4BishopTailConvergence q unit envelope =
  Complex.complexSeriesLimitConvergence
    (e4BishopTerm q)
    (e4BishopComponentwiseAbsoluteConvergence q unit envelope)

e6BishopUnsignedTailConvergence :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.ComplexSeriesConvergesTo
    (e6BishopUnsignedTerm q)
    (e6BishopUnsignedTailLimit q unit envelope)
e6BishopUnsignedTailConvergence q unit envelope =
  Complex.complexSeriesLimitConvergence
    (e6BishopUnsignedTerm q)
    (e6BishopComponentwiseAbsoluteConvergence q unit envelope)

e4BishopLimit :
  ∀ (q : Complex.BishopComplex) {ratio} →
  (unit : Unit.BishopUnitIntervalRatio ratio) →
  (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e4BishopLimit q unit envelope =
  Algebra.oneC Algebra.+C e4BishopTailLimit q unit envelope

e6BishopLimit :
  ∀ (q : Complex.BishopComplex) {ratio} →
  (unit : Unit.BishopUnitIntervalRatio ratio) →
  (envelope : BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e6BishopLimit q unit envelope =
  Algebra.oneC Algebra.-C e6BishopUnsignedTailLimit q unit envelope
