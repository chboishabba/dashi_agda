module DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact where

------------------------------------------------------------------------
-- K04d P0.01: FIXED-STAGE UNIFORM ORIGINAL FINITE LOG MODULUS.
--
-- For every N, 0<=x<=r, 0<=y=x+h<=r, the ORIGINAL source finite
-- quotient obeys
--
--   |q_L,N(x,h)-P_N(x)| <= |h|*S_N(r,0),
--
-- where P_N is the ORIGINAL derivative polynomial, S_N is the
-- finite reciprocal-weighted second quotient already constructed.
--
-- The bound is uniform in both endpoints and in the mesh increment
-- h, including h<0; it is stage-dependent. A later, independent
-- estimate S_N(r,0)<=1/[2*(1-r)^2] makes it uniform in N.
--
-- Every inequality is a native Bishop setoid order theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as Positive
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact as Explicit
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

sourceRadiusNonnegative :
  (x radius : R.ℝ) →
  R.NonNegative x →
  R._≤_ x radius →
  R.NonNegative radius
sourceRadiusNonnegative x radius xNN xInside =
  RP.0≤x⇒nonNegx
    (RP.≤-trans (RP.nonNegx⇒0≤x xNN) xInside)

sourcePowerZeroQuotientMonotone :
  (x radius : R.ℝ) →
  (xNN : R.NonNegative x) →
  (xInside : R._≤_ x radius) →
  (n : Nat) →
  R._≤_
    (Power.powerDifferenceQuotient x R.0ℝ n)
    (Power.powerDifferenceQuotient radius R.0ℝ n)
sourcePowerZeroQuotientMonotone x radius xNN xInside zero =
  RP.≤-refl
sourcePowerZeroQuotientMonotone x radius xNN xInside (suc n) =
  let
    radiusNN = sourceRadiusNonnegative x radius xNN xInside
    qx = Power.powerDifferenceQuotient x R.0ℝ n
    qr = Power.powerDifferenceQuotient radius R.0ℝ n
    xPlusZeroNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ x)) xNN
    radiusPlusZeroNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ radius)) radiusNN
    factorOrder =
      RP.≤-trans
        (RP.*-monoˡ-≤-nonNeg
          (RP.+-mono-≤ xInside RP.≤-refl)
          (Positive.originalPowerZeroStepQuotientNonnegative
            x xNN n))
        (RP.*-monoʳ-≤-nonNeg
          (sourcePowerZeroQuotientMonotone
            x radius xNN xInside n)
          radiusPlusZeroNN)
    powerOrder = Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
      n xInside xNN
  in
  RP.+-mono-≤ factorOrder powerOrder

sourcePowerSecondQuotientMonotone :
  (x h radius : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  (n : Nat) →
  R._≤_
    (Second.sourcePowerSecondQuotient x h n)
    (Second.sourcePowerSecondQuotient radius R.0ℝ n)
sourcePowerSecondQuotientMonotone
    x h radius xNN yNN xInside yInside zero =
  RP.≤-refl
sourcePowerSecondQuotientMonotone
    x h radius xNN yNN xInside yInside (suc n) =
  let
    radiusNN = sourceRadiusNonnegative x radius xNN xInside
    radiusPlusZeroNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ radius)) radiusNN
    t = Second.sourcePowerSecondQuotient x h n
    tr = Second.sourcePowerSecondQuotient radius R.0ℝ n
    yInsideRadiusPlusZero =
      RP.≤-respʳ-≃
        (RP.≃-symm (RP.+-identityʳ radius))
        yInside
    firstOrder =
      RP.≤-trans
        (RP.*-monoˡ-≤-nonNeg
          yInsideRadiusPlusZero
          (Positive.originalPowerSecondQuotientNonnegative
            x h xNN yNN n))
        (RP.*-monoʳ-≤-nonNeg
          (sourcePowerSecondQuotientMonotone
            x h radius xNN yNN xInside yInside n)
          radiusPlusZeroNN)
    secondOrder = sourcePowerZeroQuotientMonotone
      x radius xNN xInside n
  in
  RP.+-mono-≤ firstOrder secondOrder

sourceFiniteLogSecondQuotientMonotone :
  (x h radius : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  (n : Nat) →
  R._≤_
    (Second.sourceFiniteLogSecondQuotient x h n)
    (Second.sourceFiniteLogSecondQuotient radius R.0ℝ n)
sourceFiniteLogSecondQuotientMonotone
    x h radius xNN yNN xInside yInside zero =
  RP.≤-refl
sourceFiniteLogSecondQuotientMonotone
    x h radius xNN yNN xInside yInside (suc n) =
  RP.+-mono-≤
    (sourceFiniteLogSecondQuotientMonotone
      x h radius xNN yNN xInside yInside n)
    (RP.*-monoˡ-≤-nonNeg
      (sourcePowerSecondQuotientMonotone
        x h radius xNN yNN xInside yInside (suc n))
      (Recip.reciprocalNonnegative n))

originalFiniteLogPolynomialQuotientUniformModulus :
  (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  (n : Nat) →
  R._≤_
    (R.∣ R._-_
      (Explicit.originalSourceFiniteLogQuotient n x h)
      (Geo.negativeLogDerivativePolynomial x n) ∣)
    (R._*_
      (R.∣ h ∣)
      (Second.sourceFiniteLogSecondQuotient radius R.0ℝ n))
originalFiniteLogPolynomialQuotientUniformModulus
    radius x h xNN yNN xInside yInside n =
  let
    s = Second.sourceFiniteLogSecondQuotient x h n
    radiusS = Second.sourceFiniteLogSecondQuotient radius R.0ℝ n
    absEquality =
      RP.≃-trans
        (RP.∣-∣-cong
          (Positive.originalFiniteLogPolynomialQuotientDefectEqualsStep
            x h n))
        (RP.≃-trans
          (RP.∣x*y∣≃∣x∣*∣y∣ h s)
          (RP.*-cong
            RP.≃-refl
            (RP.nonNegx⇒∣x∣≃x
              (Positive.originalFiniteLogSecondQuotientNonnegative
                x h xNN yNN n))))
    bound = RP.*-monoˡ-≤-nonNeg
      (sourceFiniteLogSecondQuotientMonotone
        x h radius xNN yNN xInside yInside n)
      (RP.nonNeg∣x∣ h)
  in
  RP.≤-respˡ-≃ absEquality bound
