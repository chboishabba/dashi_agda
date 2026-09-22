module DASHI.Moonshine.EisensteinQExponentCartesianExact where

------------------------------------------------------------------------
-- PURE-ALGEBRA q-EXPONENT CARTESIAN IDENTITY
--
-- For tau = x + i y and p = pi,
--
--   2 p i tau = -(2 p)y + i (2 p)x.
--
-- This theorem uses only the literal ConcreteComplex multiplication,
-- scaleNatC 2, and the already-owned real ring-normalisation laws.  It does
-- not use positivity, a modulus, square roots, exp-additivity, or convergence.
--
-- Therefore the q-disk frontier can no longer count the Cartesian exponent
-- identity as an analytic input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

private
  RealCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  RealCarrier C =
    Real.Real (Real.real (Complex.realPackage C))

  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

mulZeroLeftFromRing :
  ∀ {R} →
  Ring.ConstructedRealRingNormalisationLaws R →
  (x : Real.Real R) →
  Real._*_ R (Real.zero R) x ≡ Real.zero R
mulZeroLeftFromRing {R} laws x =
  trans
    (Real.mulComm R (Real.zero R) x)
    (Ring.mulZeroRightLaw laws x)

twoPi :
  (C : Complex.ConstructedComplexPackage) →
  RealCarrier C
twoPi C =
  let
    R = Real.real (Complex.realPackage C)
    p = Complex.pi (Complex.complexExponential C)
  in
  Real._+_ R p p

imaginaryTimesPi :
  (C : Complex.ConstructedComplexPackage) →
  (ring :
    Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C))) →
  Complex._*C_
    Complex.imaginaryUnit
    (Complex.complex
      (Complex.pi (Complex.complexExponential C))
      (Real.zero (Real.real (Complex.realPackage C))))
  ≡
  Complex.complex
    (Real.zero (Real.real (Complex.realPackage C)))
    (Complex.pi (Complex.complexExponential C))
imaginaryTimesPi C ring =
  let
    R = Real.real (Complex.realPackage C)
    p = Complex.pi (Complex.complexExponential C)
    A = Complex.algebraLaws C
  in
  case refl of λ where
    refl →
      trans
        refl
        (let
          -- Kept as a rewrite proof so the literal ConcreteComplex formula,
          -- rather than a second complex multiplication implementation, owns
          -- the identity.
          in
          proof R p A)
  where
  proof :
    (R : Real.ConstructedOrderedCompleteReal) →
    (p : Real.Real R) →
    Complex.ComplexAlgebraLaws R →
    Complex.complex
      (Real._-_ R
        (Real._*_ R (Real.zero R) p)
        (Real._*_ R (Real.one R) (Real.zero R)))
      (Real._+_ R
        (Real._*_ R (Real.zero R) (Real.zero R))
        (Real._*_ R (Real.one R) p))
    ≡
    Complex.complex (Real.zero R) p
  proof R p A
    rewrite mulZeroLeftFromRing ring p
          | Ring.mulZeroRightLaw ring (Real.one R)
          | Real.subSelf R (Real.zero R)
          | mulZeroLeftFromRing ring (Real.zero R)
          | Real.mulOneLeft R p
          | Real.addZeroLeft R p = refl

twoPiImaginary :
  (C : Complex.ConstructedComplexPackage) →
  (ring :
    Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C))) →
  Q.scaleNatC 2
    (Complex._*C_
      Complex.imaginaryUnit
      (Complex.complex
        (Complex.pi (Complex.complexExponential C))
        (Real.zero (Real.real (Complex.realPackage C)))))
  ≡
  Complex.complex
    (Real.zero (Real.real (Complex.realPackage C)))
    (twoPi C)
twoPiImaginary C ring
  rewrite imaginaryTimesPi C ring
        | Real.addZeroRight
            (Real.real (Complex.realPackage C))
            (Real.zero (Real.real (Complex.realPackage C)))
        | Real.addZeroRight
            (Real.real (Complex.realPackage C))
            (Complex.pi (Complex.complexExponential C))
        | Real.addZeroRight
            (Real.real (Complex.realPackage C))
            (Real.zero (Real.real (Complex.realPackage C))) = refl

qExponentCartesianFromRing :
  (C : Complex.ConstructedComplexPackage) →
  (ring :
    Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C))) →
  (tau : ComplexCarrier C) →
  Complex._*C_
    (Q.scaleNatC 2
      (Complex._*C_
        Complex.imaginaryUnit
        (Complex.complex
          (Complex.pi (Complex.complexExponential C))
          (Real.zero (Real.real (Complex.realPackage C))))))
    tau
  ≡
  Complex.complex
    (Real.neg
      (Real.real (Complex.realPackage C))
      (Real._*_
        (Real.real (Complex.realPackage C))
        (twoPi C)
        (Complex.im tau)))
    (Real._*_
      (Real.real (Complex.realPackage C))
      (twoPi C)
      (Complex.re tau))
qExponentCartesianFromRing C ring (Complex.complex x y)
  rewrite twoPiImaginary C ring
        | mulZeroLeftFromRing ring x
        | Complex.zeroSub (Complex.algebraLaws C)
            (Real._*_
              (Real.real (Complex.realPackage C))
              (twoPi C) y)
        | mulZeroLeftFromRing ring y
        | Real.addZeroLeft
            (Real.real (Complex.realPackage C))
            (Real._*_
              (Real.real (Complex.realPackage C))
              (twoPi C) x) = refl

record EisensteinQExponentCartesianBoundary : Set where
  constructor eisenstein-q-exponent-cartesian-boundary
  field
    imaginaryTimesPiPaid : Bool
    scaleTwoPiPaid : Bool
    cartesianExponentPaid : Bool
    positivityUsed : Bool
    modulusUsed : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open EisensteinQExponentCartesianBoundary public

canonicalEisensteinQExponentCartesianBoundary :
  EisensteinQExponentCartesianBoundary
canonicalEisensteinQExponentCartesianBoundary =
  eisenstein-q-exponent-cartesian-boundary
    true true true false false
