module DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact where

------------------------------------------------------------------------
-- BISHOP q-EXPONENT MAGNITUDE -> LITERAL q REAL-EXPONENT COMPILER
--
-- DASHI CONTRIBUTION
--
-- The legacy ConcreteComplex lane already proves exactly
--
--   Re((2*pi*i)tau) = -(2*pi*Im tau).
--
-- Therefore a cross-carrier q-exponent proof need not start from the complex
-- product.  It is enough to supply:
--
--   * a map from Bishop reals into the legacy real carrier;
--   * same-object agreement for the positive magnitude 2*pi*Im tau;
--   * preservation of negation at that magnitude.
--
-- This compiler then produces the exact exponentAgreement consumed by
-- JInvariantLiteralQBishopRadiusSameObjectReductionExact.
--
-- No pi identity, imaginary-coordinate identity, or exponential identity is
-- inferred here; those remain the semantic producers of magnitudeAgreement
-- and the later exponentialAgreement respectively.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantQExponentCartesianNormalizationExact as Cartesian
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as Q
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as BishopRadius

qExponentMagnitude : BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
qExponentMagnitude = BishopRadius.qExponentMagnitude

record QBishopExponentMagnitudeTransport
    (C : Complex.ConstructedComplexPackage)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (piB imagB : BishopReal.ℝ) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)

  field
    toLegacy : BishopReal.ℝ → Real.Real R

    magnitudeAgreement :
      toLegacy (qExponentMagnitude piB imagB)
      ≡
      Real._*_ R
        (Cartesian.twoPi C)
        (Complex.im tau)

    negAgreement :
      toLegacy
        (BishopReal.-_ (qExponentMagnitude piB imagB))
      ≡
      Real.neg R
        (toLegacy (qExponentMagnitude piB imagB))

open QBishopExponentMagnitudeTransport public

compileExponentAgreement :
  ∀ {C : Complex.ConstructedComplexPackage}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : QBishopExponentMagnitudeTransport C tau piB imagB) →
  toLegacy transport
    (BishopReal.-_ (qExponentMagnitude piB imagB))
  ≡
  Complex.re (Q.qExponent C tau)
compileExponentAgreement {C} N tau {piB} {imagB} transport =
  trans
    (negAgreement transport)
    (trans
      (cong
        (Real.neg (Real.real (Complex.realPackage C)))
        (magnitudeAgreement transport))
      (sym (Cartesian.qExponentRealPartExact C N tau)))
