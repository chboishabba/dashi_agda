module DASHI.Moonshine.JInvariantQBishopMagnitudeCoordinateTransportExact where

------------------------------------------------------------------------
-- BISHOP 2*pi*Im COORDINATES -> LITERAL q MAGNITUDE TRANSPORT
--
-- DASHI CONTRIBUTION
--
-- This owner decomposes the remaining positive q-exponent magnitude weld.
-- A caller supplies only the cross-carrier real map together with:
--
--   * agreement of Bishop 2 with legacy 1+1;
--   * agreement of the chosen Bishop pi-candidate with legacy pi;
--   * agreement of the Bishop imaginary coordinate with literal Im(tau);
--   * multiplication preservation;
--   * negation preservation at the final magnitude.
--
-- Legacy distributivity and unit laws then derive
--
--   map((2*pi_B)*Im_B tau) = (pi+pi)*Im tau,
--
-- which is exactly the magnitude consumed by the already-owned Cartesian
-- q-exponent normalization theorem.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans)

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantQExponentCartesianNormalizationExact as Cartesian
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as BishopRadius
import DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact as Exponent

record QBishopMagnitudeCoordinateTransport
    (C : Complex.ConstructedComplexPackage)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (piB imagB : BishopReal.ℝ) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)

  field
    toLegacy : BishopReal.ℝ → Real.Real R

    twoAgreement :
      toLegacy BishopRadius.two
      ≡
      Real._+_ R (Real.one R) (Real.one R)

    piAgreement :
      toLegacy piB
      ≡
      Complex.pi (Complex.complexExponential C)

    imagAgreement :
      toLegacy imagB
      ≡
      Complex.im tau

    mulAgreement :
      ∀ left right →
      toLegacy (BishopReal._*_ left right)
      ≡
      Real._*_ R (toLegacy left) (toLegacy right)

    negAgreement :
      toLegacy
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB))
      ≡
      Real.neg R
        (toLegacy
          (BishopRadius.qExponentMagnitude piB imagB))

open QBishopMagnitudeCoordinateTransport public

legacyDoubleTimesPiIsTwoPi :
  ∀ {C : Complex.ConstructedComplexPackage} →
  let
    R = Real.real (Complex.realPackage C)
    p = Complex.pi (Complex.complexExponential C)
  in
  Real._*_ R
    (Real._+_ R (Real.one R) (Real.one R))
    p
  ≡
  Cartesian.twoPi C
legacyDoubleTimesPiIsTwoPi {C} =
  let
    R = Real.real (Complex.realPackage C)
    p = Complex.pi (Complex.complexExponential C)
  in
  trans
    (Real.distribRight R (Real.one R) (Real.one R) p)
    (cong₂
      (Real._+_ R)
      (Real.mulOneLeft R p)
      (Real.mulOneLeft R p))

compileMagnitudeAgreement :
  ∀ {C : Complex.ConstructedComplexPackage}
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : QBishopMagnitudeCoordinateTransport C tau piB imagB) →
  toLegacy transport
    (BishopRadius.qExponentMagnitude piB imagB)
  ≡
  Real._*_ (Real.real (Complex.realPackage C))
    (Cartesian.twoPi C)
    (Complex.im tau)
compileMagnitudeAgreement {C} tau {piB} {imagB} transport =
  let
    R = Real.real (Complex.realPackage C)
    p = Complex.pi (Complex.complexExponential C)

    innerAgreement :
      toLegacy transport
        (BishopReal._*_ BishopRadius.two piB)
      ≡
      Cartesian.twoPi C
    innerAgreement =
      trans
        (mulAgreement transport BishopRadius.two piB)
        (trans
          (cong₂
            (Real._*_ R)
            (twoAgreement transport)
            (piAgreement transport))
          (legacyDoubleTimesPiIsTwoPi {C}))

  in
  trans
    (mulAgreement transport
      (BishopReal._*_ BishopRadius.two piB)
      imagB)
    (trans
      (cong₂
        (Real._*_ R)
        innerAgreement
        (imagAgreement transport))
      (cong
        (λ right → Real._*_ R (Cartesian.twoPi C) right)
        (Real.addZeroRight R (Complex.im tau))))

compileExponentMagnitudeTransport :
  ∀ {C : Complex.ConstructedComplexPackage}
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ} →
  QBishopMagnitudeCoordinateTransport C tau piB imagB →
  Exponent.QBishopExponentMagnitudeTransport C tau piB imagB
compileExponentMagnitudeTransport tau transport = record
  { Exponent.toLegacy = toLegacy transport
  ; Exponent.magnitudeAgreement =
      compileMagnitudeAgreement tau transport
  ; Exponent.negAgreement = negAgreement transport
  }
