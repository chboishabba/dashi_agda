{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopMachinExistingCayleyReuseExact where

------------------------------------------------------------------------
-- K05-PI: REUSE PRIOR CAYLEY/PYTHAGOREAN AND RATIONAL COMPLEX OWNERS.
--
-- Existing prior-art sources:
--   BalabanSelectedGaugeRedundancyHolonomyGuardExact:
--      U(t) = ((1-t²)/(1+t²), 2t/(1+t²), 0, 0)
--      at t = 1/8192, with exact rational unit norm.
--   CayleyDicksonRationalComplexQuaternionExact:
--      ORIGINAL rational complex pair, multiplication, conjugation,
--      norm composition, and literal quaternion identification.
--   BishopMachinRationalGaussianPhaseExact:
--      exact Machin t=1/5, t=1/239 numerical Cayley certificates.
--
-- This module identifies the rational Cayley numerator/denominator
-- algebra on that original rational complex carrier, including the
-- same finite quaternion used by the pre-existing Yang--Mills guard.
-- It then composes the two original rational complex phases using
-- the EXISTING complex multiplication, not a second Gaussian carrier.
--
-- This is purely finite Q[i]. The ORIGINAL Bishop equation
--   exp_C(2*i*atan_B(t)) ~= (1+i*t)/(1-i*t)
-- remains an analytic same-object theorem obligation. No replacement
-- Bishop real, new complex carrier, trigonometric axiom, or ad-hoc
-- classical branch is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Physics.YangMills.BalabanSelectedGaugeRedundancyHolonomyGuardExact as Guard
import DASHI.Foundations.BishopMachinRationalGaussianPhaseExact as Machin

-- Pythagorean numerator is the original Cayley convention:
-- (1-t²) + 2it; denominator is (1+t²).
cayleyNumerator : ℚ → CD.RationalComplex
cayleyNumerator t =
  CD.complex (1ℚ - t * t) ((+ 2 / 1) * t)

cayleyDenominator : ℚ → ℚ
cayleyDenominator t = 1ℚ + t * t

-- A universal polynomial identity, needing no division and no
-- nonzero hypothesis on a generic t.
cayleyNumeratorPythagorean :
  (t : ℚ) →
  CD.complexNormSq (cayleyNumerator t)
  ≡ cayleyDenominator t * cayleyDenominator t
cayleyNumeratorPythagorean t = ℚRing.solve-∀

-- The *existing* YM exact Cayley witness is literally the original
-- quaternion embedding of the selected rational complex pair.
guardCayleyIsOriginalComplexQuaternion :
  CD.doubleToQuaternion
    (CD.pairC
      (CD.complex Guard.nearIdentityScalar Guard.nearIdentityX)
      CD.zeroC)
  ≡ Guard.nearIdentityUnit
guardCayleyIsOriginalComplexQuaternion = refl

machinFiveHalfAngle machin239HalfAngle : ℚ
machinFiveHalfAngle = + 1 / 5
machin239HalfAngle = + 1 / 239

-- We use the same original complex type and operations everywhere.
fivePhase twoHundredThirtyNinePhase : CD.RationalComplex
fivePhase =
  CD.complex Machin.phaseFiveReal Machin.phaseFiveImag
twoHundredThirtyNinePhase =
  CD.complex Machin.phase239Real Machin.phase239Imag

-- Avoid a new generic rational division operator: the finite
-- equalities are the literal Cayley numerator/denominator relations.
fivePhaseIsCayleyRealNumerator :
  CD.re fivePhase * cayleyDenominator machinFiveHalfAngle
  ≡ CD.re (cayleyNumerator machinFiveHalfAngle)
fivePhaseIsCayleyRealNumerator = ℚRing.solve-∀

fivePhaseIsCayleyImagNumerator :
  CD.im fivePhase * cayleyDenominator machinFiveHalfAngle
  ≡ CD.im (cayleyNumerator machinFiveHalfAngle)
fivePhaseIsCayleyImagNumerator = ℚRing.solve-∀

twoHundredThirtyNinePhaseIsCayleyRealNumerator :
  CD.re twoHundredThirtyNinePhase *
    cayleyDenominator machin239HalfAngle
  ≡ CD.re (cayleyNumerator machin239HalfAngle)
twoHundredThirtyNinePhaseIsCayleyRealNumerator = ℚRing.solve-∀

twoHundredThirtyNinePhaseIsCayleyImagNumerator :
  CD.im twoHundredThirtyNinePhase *
    cayleyDenominator machin239HalfAngle
  ≡ CD.im (cayleyNumerator machin239HalfAngle)
twoHundredThirtyNinePhaseIsCayleyImagNumerator = ℚRing.solve-∀

fivePhaseUnitNorm :
  CD.complexNormSq fivePhase ≡ 1ℚ
fivePhaseUnitNorm = Machin.phaseFiveUnitModulus

twoHundredThirtyNinePhaseUnitNorm :
  CD.complexNormSq twoHundredThirtyNinePhase ≡ 1ℚ
twoHundredThirtyNinePhaseUnitNorm = Machin.phase239UnitModulus

fivePhaseSquared : CD.RationalComplex
fivePhaseSquared = CD._*c_ fivePhase fivePhase

fivePhaseFourth : CD.RationalComplex
fivePhaseFourth = CD._*c_ fivePhaseSquared fivePhaseSquared

machinQuarterCayleyPhase : CD.RationalComplex
machinQuarterCayleyPhase =
  CD._*c_
    fivePhaseFourth
    (CD.conjugateC twoHundredThirtyNinePhase)

-- Reuse both the previous all-rational exact coefficient proofs AND
-- the original rational complex multiplication and conjugation.
originalComplexQuarterRealIsExistingCertificate :
  CD.re machinQuarterCayleyPhase ≡ Machin.machinQuarterGaussianReal
originalComplexQuarterRealIsExistingCertificate = ℚRing.solve-∀

originalComplexQuarterImagIsExistingCertificate :
  CD.im machinQuarterCayleyPhase ≡ Machin.machinQuarterGaussianImag
originalComplexQuarterImagIsExistingCertificate = ℚRing.solve-∀

originalComplexMachinQuarterCayleyIsImaginaryUnit :
  machinQuarterCayleyPhase ≡ CD.complex 0ℚ 1ℚ
originalComplexMachinQuarterCayleyIsImaginaryUnit =
  CD.complexExt
    (trans
      originalComplexQuarterRealIsExistingCertificate
      Machin.machinQuarterGaussianRealZero)
    (trans
      originalComplexQuarterImagIsExistingCertificate
      Machin.machinQuarterGaussianImagOne)

-- Independent source-native norm proof: reuse the ORIGINAL
-- Cayley-Dickson rational complex norm composition, not a second
-- Pythagorean normalizer. These equations hold on the very same
-- RationalComplex carrier as the Yang--Mills quaternion owner.
oneTimesOne : 1ℚ * 1ℚ ≡ 1ℚ
oneTimesOne = ℚRing.solve-∀

fivePhaseSquaredUnit :
  CD.complexNormSq fivePhaseSquared ≡ 1ℚ
fivePhaseSquaredUnit =
  trans
    (CD.complexNormMultiplicative fivePhase fivePhase)
    (trans
      (cong₂ _*_ fivePhaseUnitNorm fivePhaseUnitNorm)
      oneTimesOne)

fivePhaseFourthUnit :
  CD.complexNormSq fivePhaseFourth ≡ 1ℚ
fivePhaseFourthUnit =
  trans
    (CD.complexNormMultiplicative fivePhaseSquared fivePhaseSquared)
    (trans
      (cong₂ _*_ fivePhaseSquaredUnit fivePhaseSquaredUnit)
      oneTimesOne)

conjugateComplexNormSame :
  (z : CD.RationalComplex) →
  CD.complexNormSq (CD.conjugateC z) ≡ CD.complexNormSq z
conjugateComplexNormSame (CD.complex a b) = ℚRing.solve-∀

twoHundredThirtyNineConjugateUnit :
  CD.complexNormSq (CD.conjugateC twoHundredThirtyNinePhase) ≡ 1ℚ
twoHundredThirtyNineConjugateUnit =
  trans
    (conjugateComplexNormSame twoHundredThirtyNinePhase)
    twoHundredThirtyNinePhaseUnitNorm

originalComplexMachinQuarterHasUnitNorm :
  CD.complexNormSq machinQuarterCayleyPhase ≡ 1ℚ
originalComplexMachinQuarterHasUnitNorm =
  trans
    (CD.complexNormMultiplicative
      fivePhaseFourth
      (CD.conjugateC twoHundredThirtyNinePhase))
    (trans
      (cong₂ _*_
        fivePhaseFourthUnit
        twoHundredThirtyNineConjugateUnit)
      oneTimesOne)

-- An independent check of the same norm is also available from
-- originalComplexMachinQuarterCayleyIsImaginaryUnit + complexNormSq.
