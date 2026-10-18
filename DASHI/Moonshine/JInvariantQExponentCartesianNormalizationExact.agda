module DASHI.Moonshine.JInvariantQExponentCartesianNormalizationExact where

------------------------------------------------------------------------
-- EXACT CARTESIAN NORMALIZATION OF THE LITERAL q EXPONENT
--
-- The existing q producer uses
--
--   (2 * (i*pi)) * tau.
--
-- On the existing ConcreteComplex carrier, ordinary ring normalization is
-- enough to prove constructively
--
--   2*i*pi = (0, 2*pi)
--
-- and therefore
--
--   (2*pi*i) * (a,b) = (-(2*pi*b), 2*pi*a).
--
-- No order, trigonometric, exponential, modular-form, or source theorem enters
-- this calculation.  The only extra laws beyond ConstructedRealSpine are the
-- repo's existing `ConstructedRealRingNormalisationLaws`, used for x*0=0 and
-- subtraction-as-add-neg.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; trans)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteQ
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as Q

piC :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
piC C =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
  in
  Complex.complex (Complex.pi CE) (Real.zero R)

twoPi :
  (C : Complex.ConstructedComplexPackage) →
  Real.Real (Real.real (Complex.realPackage C))
twoPi C =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
  in
  Real._+_ R (Complex.pi CE) (Complex.pi CE)

iPi :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
iPi C = Complex._*C_ Complex.imaginaryUnit (piC C)

twoPiI :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
twoPiI C = FiniteQ.scaleNatC 2 (iPi C)

zeroMul :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Ring.ConstructedRealRingNormalisationLaws R →
  (x : Real.Real R) →
  Real._*_ R (Real.zero R) x ≡ Real.zero R
zeroMul {R} N x =
  trans
    (Real.mulComm R (Real.zero R) x)
    (Ring.mulZeroRightLaw N x)

iPiExact :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  iPi C
  ≡ Complex.complex
      (Real.zero (Real.real (Complex.realPackage C)))
      (Complex.pi (Complex.complexExponential C))
iPiExact C N =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    p = Complex.pi CE
    realPart :
      Real._-_ R
        (Real._*_ R (Real.zero R) p)
        (Real._*_ R (Real.one R) (Real.zero R))
      ≡ Real.zero R
    realPart =
      trans
        (cong₂ (Real._-_ R)
          (zeroMul N p)
          (Ring.mulZeroRightLaw N (Real.one R)))
        (Real.subSelf R (Real.zero R))

    imagPart :
      Real._+_ R
        (Real._*_ R (Real.zero R) (Real.zero R))
        (Real._*_ R (Real.one R) p)
      ≡ p
    imagPart =
      trans
        (cong₂ (Real._+_ R)
          (zeroMul N (Real.zero R))
          (Real.mulOneLeft R p))
        (Real.addZeroLeft R p)
  in
  cong₂ Complex.complex realPart imagPart

twoPiIExact :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  twoPiI C
  ≡ Complex.complex
      (Real.zero (Real.real (Complex.realPackage C)))
      (twoPi C)
twoPiIExact C N =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    p = Complex.pi CE

    normalizedScale :
      FiniteQ.scaleNatC 2
        (Complex.complex (Real.zero R) p)
      ≡ Complex.complex (Real.zero R) (Real._+_ R p p)
    normalizedScale =
      cong₂ Complex.complex
        (trans
          (cong
            (λ tail → Real._+_ R (Real.zero R) tail)
            (Real.addZeroRight R (Real.zero R)))
          (Real.addZeroRight R (Real.zero R)))
        (cong
          (λ tail → Real._+_ R p tail)
          (Real.addZeroRight R p))
  in
  trans
    (cong (FiniteQ.scaleNatC 2) (iPiExact C N))
    normalizedScale

qExponentCartesianExact :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Q.qExponent C tau
  ≡ Complex.complex
      (Real.neg (Real.real (Complex.realPackage C))
        (Real._*_ (Real.real (Complex.realPackage C))
          (twoPi C)
          (Complex.im tau)))
      (Real._*_ (Real.real (Complex.realPackage C))
        (twoPi C)
        (Complex.re tau))
qExponentCartesianExact C N tau =
  let
    R = Real.real (Complex.realPackage C)
    a = Complex.re tau
    b = Complex.im tau
    p2 = twoPi C

    realPart :
      Real._-_ R
        (Real._*_ R (Real.zero R) a)
        (Real._*_ R p2 b)
      ≡ Real.neg R (Real._*_ R p2 b)
    realPart =
      trans
        (cong
          (λ left → Real._-_ R left (Real._*_ R p2 b))
          (zeroMul N a))
        (trans
          (Ring.subAsAddNeg N (Real.zero R) (Real._*_ R p2 b))
          (Real.addZeroLeft R (Real.neg R (Real._*_ R p2 b))))

    imagPart :
      Real._+_ R
        (Real._*_ R (Real.zero R) b)
        (Real._*_ R p2 a)
      ≡ Real._*_ R p2 a
    imagPart =
      trans
        (cong
          (λ left → Real._+_ R left (Real._*_ R p2 a))
          (zeroMul N b))
        (Real.addZeroLeft R (Real._*_ R p2 a))
  in
  trans
    (cong (λ factor → Complex._*C_ factor tau) (twoPiIExact C N))
    (cong₂ Complex.complex realPart imagPart)

qExponentRealPartExact :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Complex.re (Q.qExponent C tau)
  ≡ Real.neg (Real.real (Complex.realPackage C))
      (Real._*_ (Real.real (Complex.realPackage C))
        (twoPi C)
        (Complex.im tau))
qExponentRealPartExact C N tau =
  cong Complex.re (qExponentCartesianExact C N tau)
