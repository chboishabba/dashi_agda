module DASHI.Mathematics.Automorphic.EllipticCMLevel32EtaNewmanArithmeticExact where

------------------------------------------------------------------------
-- E:y²=x³-x: level-32 eta(4z)² eta(8z)² arithmetic preflight.
--
-- Newman/Gordon-Hughes eta-quotient arithmetic conditions for
-- N=32, r4=r8=2:
--   sum_d d r_d ≡ 0 mod 24,
--   sum_d (N/d) r_d ≡ 0 mod 24,
--   product_d d^r_d is a rational square,
--   (sum r_d)/2 = weight 2.
--
-- All the actual numbers are computed as EXACT NAT equality,
-- with no synthetic modularity proof fields.
-- These are the finite arithmetic conditions, NOT proof of
-- the analytic eta transformation law, holomorphy at all cusps,
-- exact normalized newform status, CM character identification,
-- or the elliptic curve Mellin L-function.
--
-- The q-leading exponent is (4*2+8*2)/24 = 1, providing
-- a precise same-newform normalization target to the original
-- Gaussian Jacobi theta coefficient q^1 = 1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Mathematics.Automorphic.EllipticCMJacobiThetaCheckedRowsExact as Theta
import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact as Frobenius
open import Data.Rational.Base using (1ℚ)
open import Data.Product using (_×_; _,_)

level : Nat
level = 32

etaScaleFour : Nat
etaScaleFour = 4

etaScaleEight : Nat
etaScaleEight = 8

etaExponentAtFour : Nat
etaExponentAtFour = 2

etaExponentAtEight : Nat
etaExponentAtEight = 2

etaWeightTwice : Nat
etaWeightTwice = etaExponentAtFour + etaExponentAtEight

etaWeightTwo : etaWeightTwice ≡ 2 * 2
etaWeightTwo = refl

etaWeightedExponentSum : Nat
etaWeightedExponentSum =
  etaScaleFour * etaExponentAtFour +
  etaScaleEight * etaExponentAtEight

etaLeadingExponentIsTwentyFour :
  etaWeightedExponentSum ≡ 24
etaLeadingExponentIsTwentyFour = refl

etaDualWeightedExponentSum : Nat
etaDualWeightedExponentSum =
  8 * etaExponentAtFour + 4 * etaExponentAtEight

etaDualExponentIsTwentyFour :
  etaDualWeightedExponentSum ≡ 24
etaDualExponentIsTwentyFour = refl

etaScaleProductSquared : Nat
etaScaleProductSquared =
  (etaScaleFour * etaScaleFour)
  * (etaScaleEight * etaScaleEight)

etaScaleProductIsSquare :
  etaScaleProductSquared ≡ 32 * 32
etaScaleProductIsSquare = refl

level32HasCorrectScales :
  level ≡ etaScaleFour * etaScaleEight
level32HasCorrectScales = refl

-- Explicit arithmetic congruences are strengthened to equality,
-- so no modulo-24 machinery or decidable residue oracle is needed.
etaNewmanArithmeticConditions :
  etaWeightTwice ≡ 4
  × etaWeightedExponentSum ≡ 24
  × etaDualWeightedExponentSum ≡ 24
  × etaScaleProductSquared ≡ 32 * 32
etaNewmanArithmeticConditions = refl , refl , refl , refl

-- The independent theta calculation is attached to the
-- correctly normalized q-leading coefficient of this EXACT
-- exponent vector, not to an unrelated weight-two candidate.
level32ThetaLeadingCoefficientMatchesNormalization :
  Theta.cmThetaCoefficientThrough19 1 ≡ 1ℚ
level32ThetaLeadingCoefficientMatchesNormalization =
  Theta.thetaNormalizedFirstCoefficient

level32ThetaP5MatchesOriginalCurve :
  Theta.cmThetaCoefficientThrough19 5
  ≡ Frobenius.signedToRational
      (Frobenius.frobeniusTrace Frobenius.p5Row)
level32ThetaP5MatchesOriginalCurve =
  Theta.thetaP5MatchesOriginalFrobenius
