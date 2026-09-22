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
import DASHI.Moonshine.EisensteinUpperHalfPlaneQDiskExact as QDisk

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
imaginaryTimesPi C ring
  rewrite mulZeroLeftFromRing ring
            (Complex.pi (Complex.complexExponential C))
        | Ring.mulZeroRightLaw ring
            (Real.one (Real.real (Complex.realPackage C)))
        | Real.subSelf
            (Real.real (Complex.realPackage C))
            (Real.zero (Real.real (Complex.realPackage C)))
        | mulZeroLeftFromRing ring
            (Real.zero (Real.real (Complex.realPackage C)))
        | Real.mulOneLeft
            (Real.real (Complex.realPackage C))
            (Complex.pi (Complex.complexExponential C))
        | Real.addZeroLeft
            (Real.real (Complex.realPackage C))
            (Complex.pi (Complex.complexExponential C)) = refl

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


------------------------------------------------------------------------
-- The remaining QDisk laws after Cartesian algebra has been discharged.
------------------------------------------------------------------------

record QDiskResidualAnalyticLaws
    (C : Complex.ConstructedComplexPackage) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)
    E = Real.exponential (Complex.realPackage C)
    CE = Complex.complexExponential C

  field
    twoPiPositive :
      Real._<_ R (Real.zero R) (twoPi C)

    positiveProduct :
      ∀ {x y} →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.zero R) y →
      Real._<_ R (Real.zero R) (Real._*_ R x y)

    negativeOfPositiveIsNegative :
      ∀ {x} →
      Real._<_ R (Real.zero R) x →
      Real._<_ R (Real.neg R x) (Real.zero R)

    modulus : ComplexCarrier C → RealCarrier C

    modulusOfComplexExponential :
      (x y : RealCarrier C) →
      modulus
        (Complex.expC CE (Complex.complex x y))
      ≡ Real.exp E x

open QDiskResidualAnalyticLaws public

qDiskAnalyticLawsFromRingAndResidual :
  (C : Complex.ConstructedComplexPackage) →
  Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C)) →
  QDiskResidualAnalyticLaws C →
  QDisk.QDiskAnalyticLaws C
qDiskAnalyticLawsFromRingAndResidual C ring residual =
  record
    { QDisk.twoPi = twoPi C
    ; QDisk.twoPiDefinition = refl
    ; QDisk.twoPiPositive = twoPiPositive residual
    ; QDisk.positiveProduct = positiveProduct residual
    ; QDisk.negativeOfPositiveIsNegative =
        negativeOfPositiveIsNegative residual
    ; QDisk.qExponentCartesian =
        qExponentCartesianFromRing C ring
    ; QDisk.modulus = modulus residual
    ; QDisk.modulusOfComplexExponential =
        modulusOfComplexExponential residual
    }

record EisensteinQExponentCartesianBoundary : Set where
  constructor eisenstein-q-exponent-cartesian-boundary
  field
    imaginaryTimesPiPaid : Bool
    scaleTwoPiPaid : Bool
    cartesianExponentPaid : Bool
    fullQDiskLawsCompileFromResidualAnalyticLaws : Bool
    positivityUsed : Bool
    modulusUsed : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open EisensteinQExponentCartesianBoundary public

canonicalEisensteinQExponentCartesianBoundary :
  EisensteinQExponentCartesianBoundary
canonicalEisensteinQExponentCartesianBoundary =
  eisenstein-q-exponent-cartesian-boundary
    true true true true false false
