{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySU2TraceNormalizationWeldExact where

open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact as SU2

------------------------------------------------------------------------
-- EXPLICIT 1/pi^2 NORMALIZATION WELD
--
-- The rational coefficient -11/48 is only the coefficient multiplying
-- 1/pi^2 in the repository's SU(2) convention.  This module prevents the
-- transcendental factor from disappearing behind the phrase "normalized F^2".
--
-- Work in an arbitrary scalar carrier that owns the physical inverse-pi-square.
-- A rational normalized F^2 numerator is legitimate only when its embedding is
-- exactly inversePiSquared * rawF2Numerator.  If the selected quantum trace has
-- the physical scalar identity
--
--   embed(Q) = embed(-11/48) * (inversePiSquared * rawF2),
--
-- multiplicativity and injectivity of the rational embedding recover the exact
-- rational identity
--
--   Q = (-11/48) * normalizedF2.
------------------------------------------------------------------------

record SU2TraceNormalizationWeld (Scalar : Set) : Set₁ where
  field
    embedRational : ℚ → Scalar
    multiply : Scalar → Scalar → Scalar
    inversePiSquared : Scalar

    rawF2Numerator : Scalar
    normalizedF2Numerator : ℚ
    selectedQuantumTraceNumerator : ℚ

    embedRationalMultiplicative :
      ∀ left right →
      embedRational (left * right)
      ≡ multiply (embedRational left) (embedRational right)

    embedRationalInjective :
      ∀ {left right} →
      embedRational left ≡ embedRational right →
      left ≡ right

    normalizedF2CarriesInversePiSquared :
      embedRational normalizedF2Numerator
      ≡ multiply inversePiSquared rawF2Numerator

    selectedTraceUsesPhysicalSU2Convention :
      embedRational selectedQuantumTraceNumerator
      ≡
      multiply
        (embedRational SU2.su2TraceRationalCoefficient)
        (multiply inversePiSquared rawF2Numerator)

open SU2TraceNormalizationWeld public

selectedTraceUsesNormalizedRationalF2 :
  ∀ {Scalar}
    (weld : SU2TraceNormalizationWeld Scalar) →
  selectedQuantumTraceNumerator weld
  ≡
  SU2.su2TraceRationalCoefficient * normalizedF2Numerator weld
selectedTraceUsesNormalizedRationalF2 weld =
  embedRationalInjective weld
    (trans
      (selectedTraceUsesPhysicalSU2Convention weld)
      (trans
        (cong
          (λ rhs →
            multiply weld
              (embedRational weld SU2.su2TraceRationalCoefficient)
              rhs)
          (sym (normalizedF2CarriesInversePiSquared weld)))
        (sym
          (embedRationalMultiplicative weld
            SU2.su2TraceRationalCoefficient
            (normalizedF2Numerator weld)))))

inversePiSquaredNormalizationExplicitlyPaid :
  ∀ {Scalar}
    (weld : SU2TraceNormalizationWeld Scalar) →
  embedRational weld (normalizedF2Numerator weld)
  ≡ multiply weld (inversePiSquared weld) (rawF2Numerator weld)
inversePiSquaredNormalizationExplicitlyPaid =
  normalizedF2CarriesInversePiSquared
