module DASHI.Analysis.BishopOriginalMachinSignedPowerRadiusExact where

-- SOURCE-WRITTEN / AGDA KERNEL PENDING.
-- ALL-N ABSOLUTE RADIUS DOMINANCE for the ORIGINAL Bishop polynomial
-- first and second quotient, reusing the exact K04d LOG power spine.
--
-- Let y=x+h, rho=|x|, eta=|y|, delta=eta-rho.
-- Nonnegativity of rho and eta and rho+delta≈eta is constructive.
-- Then:
--   |Q_n(x,0)| <= Q_n(rho,0)
--   |T_n(x,h)| <= T_n(rho,delta)
--   |T_n(x,h)| <= T_n(1/2,0), if |x|,|x+h|<=1/2.
-- No sign assumption on x,h; h may be zero or negative.
-- The old LOG source already pays T_n(rho,delta)<=T_n(r,0)
-- for nonnegative endpoints, so that theorem is REUSED.
--
-- All constructions use the original Bishop setoid, not abstract normed
-- fields. Kernel check remains required before claiming acceptance.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as Positive
import DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact as Radius
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

absEndpointDelta : R.ℝ → R.ℝ → R.ℝ
absEndpointDelta x h =
  R._-_ (R.∣ R._+_ x h ∣) (R.∣ x ∣)

absEndpointSum :
  (x h : R.ℝ) →
  R._≃_
    (R._+_ (R.∣ x ∣) (absEndpointDelta x h))
    (R.∣ R._+_ x h ∣)
absEndpointSum x h =
  let open P.ℝ-Solver in
  solve 2 (λ a b → a ⊕ (b ⊖ a) ⊜ b)
    P.≃-refl (R.∣ x ∣) (R.∣ R._+_ x h ∣)

-- Original zero-step polynomial quotient: absolute bound for all n.
originalZeroStepAbsoluteRadius :
  (x radius : R.ℝ) →
  (radiusNN : R.NonNegative radius) →
  (inside : R._≤_ (R.∣ x ∣) radius) →
  (n : Nat) →
  R._≤_
    (R.∣ Power.powerDifferenceQuotient x R.0ℝ n ∣)
    (Power.powerDifferenceQuotient radius R.0ℝ n)
originalZeroStepAbsoluteRadius x radius radiusNN inside zero =
  P.≤-respˡ-≃
    (P.nonNegx⇒∣x∣≃x P.nonNeg0)
    P.≤-refl
originalZeroStepAbsoluteRadius x radius radiusNN inside (suc n) =
  let
    q = Power.powerDifferenceQuotient x R.0ℝ n
    qr = Power.powerDifferenceQuotient radius R.0ℝ n
    xp = R._+_ x R.0ℝ
    rp = R._+_ radius R.0ℝ
    radiusPlusNN =
      P.nonNeg-cong
        (P.≃-symm (P.+-identityʳ radius))
        radiusNN
    xPlusInside :
      R._≤_ (R.∣ xp ∣) rp
    xPlusInside =
      P.≤-respʳ-≃
        (P.≃-symm (P.+-identityʳ radius))
        (P.≤-respˡ-≃
          (P.∣-∣-cong (P.+-identityʳ x))
          inside)
    productBound :
      R._≤_
        (R.∣ R._*_ q xp ∣)
        (R._*_ qr rp)
    productBound =
      P.≤-respˡ-≃
        (P.∣x*y∣≃∣x∣*∣y∣ q xp)
        (P.≤-trans
          (P.*-monoˡ-≤-nonNeg
            xPlusInside (P.nonNeg∣x∣ q))
          (P.*-monoʳ-≤-nonNeg
            (originalZeroStepAbsoluteRadius
              x radius radiusNN inside n)
            radiusPlusNN))
    powerBound :
      R._≤_ (R.∣ R.pow x n ∣) (R.pow radius n)
    powerBound =
      P.≤-respˡ-≃
        (Seq.∣xⁿ∣≃∣x∣ⁿ x n)
        (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
          n inside (P.nonNeg∣x∣ x))
  in
  P.≤-trans
    (P.∣x+y∣≤∣x∣+∣y∣ (R._*_ q xp) (R.pow x n))
    (P.+-mono-≤ productBound powerBound)

-- Compare the original second quotient on signed endpoints with the
-- SAME polynomial on the absolute endpoints. It is not a proxy.
originalSignedSecondBelowAbsoluteEndpoints :
  (x h : R.ℝ) (n : Nat) →
  R._≤_
    (R.∣ Second.sourcePowerSecondQuotient x h n ∣)
    (Second.sourcePowerSecondQuotient
      (R.∣ x ∣) (absEndpointDelta x h) n)
originalSignedSecondBelowAbsoluteEndpoints x h zero =
  P.≤-respˡ-≃
    (P.nonNegx⇒∣x∣≃x P.nonNeg0)
    P.≤-refl
originalSignedSecondBelowAbsoluteEndpoints x h (suc n) =
  let
    y = R._+_ x h
    rho = R.∣ x ∣
    eta = R.∣ y ∣
    delta = absEndpointDelta x h
    t = Second.sourcePowerSecondQuotient x h n
    tr = Second.sourcePowerSecondQuotient rho delta n
    q = Power.powerDifferenceQuotient x R.0ℝ n
    qr = Power.powerDifferenceQuotient rho R.0ℝ n
    rhoNN = P.nonNeg∣x∣ x
    etaNN = P.nonNeg∣x∣ y
    endpointNN =
      P.nonNeg-cong (P.≃-symm (absEndpointSum x h)) etaNN
    productBound :
      R._≤_ (R.∣ R._*_ t y ∣)
        (R._*_ tr (R._+_ rho delta))
    productBound =
      P.≤-respˡ-≃
        (P.∣x*y∣≃∣x∣*∣y∣ t y)
        (P.≤-respʳ-≃
          (P.*-cong P.≃-refl (P.≃-symm (absEndpointSum x h)))
          (P.*-monoʳ-≤-nonNeg
            (originalSignedSecondBelowAbsoluteEndpoints x h n)
            etaNN))
    zeroBound :
      R._≤_ (R.∣ q ∣) qr
    zeroBound =
      originalZeroStepAbsoluteRadius x rho rhoNN
        P.≤-refl n
  in
  P.≤-trans
    (P.∣x+y∣≤∣x∣+∣y∣ (R._*_ t y) q)
    (P.+-mono-≤ productBound zeroBound)

-- The EXISTING LOG native nonnegative-radius theorem now supplies
-- the entire signed half-ball domination without reconstructing its
-- polynomial positivity, exponent transport or mesh order.
originalSignedSecondBelowHalf :
  (x h : R.ℝ) →
  (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
  (n : Nat) →
  R._≤_
    (R.∣ Second.sourcePowerSecondQuotient x h n ∣)
    (Second.sourcePowerSecondQuotient
      Half.bishopHalf R.0ℝ n)
originalSignedSecondBelowHalf x h xInside yInside n =
  let
    rho = R.∣ x ∣
    delta = absEndpointDelta x h
    rhoNN = P.nonNeg∣x∣ x
    etaNN = P.nonNeg∣x∣ (R._+_ x h)
    endpointNN =
      P.nonNeg-cong
        (P.≃-symm (absEndpointSum x h)) etaNN
    endpointInside =
      P.≤-respˡ-≃
        (P.≃-symm (absEndpointSum x h))
        yInside
  in
  P.≤-trans
    (originalSignedSecondBelowAbsoluteEndpoints x h n)
    (Radius.sourcePowerSecondQuotientMonotone
      rho delta Half.bishopHalf
      rhoNN endpointNN xInside endpointInside n)
