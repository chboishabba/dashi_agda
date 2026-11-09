{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpUniformResidualExact where

------------------------------------------------------------------------
-- P0: UNIFORM, EXPLICIT ORIGINAL FINITE EXP-LOG RESIDUAL MAJORANT.
--
-- The exact previously proved factor-derivative residual is
--  (1-x) F_N'(x) + F_N(x) ~= x^N F_N(x),
-- where F_N = original exp_B(-sourceNegativeLogPartial_N).
--
-- This owner proves on EVERY source compact 0<x<=r<1:
--        |x^N F_N(x)| <= r^N       (N >= 1).
--
-- Crucial genuine inputs already proved on the original carrier:
--  * sourceNegativeLogTermNonnegative and monotone finite sums;
--  * sourceLogFirstPartialEqualsX;
--  * negativeExpPositive and negativeExpBelowOne;
--  * original x<=r -> x^N<=r^N;
--  * nonnegative product absolute normalization.
--
-- The cutoff r^N -> 0 is independent of x: this is the actual
-- uniform ODE residual, not just pointwise coefficient convergence.
--
-- This does not postulate FTC, integration, global ODE uniqueness,
-- nor identify exp(-L)=1-x merely from small residuals.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegativeExp
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite

-- The literal first nonzero term is exactly x; all later signed-log
-- coefficients are nonnegative on the original positive source.
originalLogFinitePartialAtLeastPoint :
  (x : R.ℝ) →
  (xNonnegative : R.NonNegative x) →
  (n : Nat) →
  R._≤_ x
    (Finite.originalLogFinitePartial x (suc n))
originalLogFinitePartialAtLeastPoint x xNonnegative zero =
  RP.≤-reflexive
    (RP.≃-symm (Log.sourceLogFirstPartialEqualsX x))
originalLogFinitePartialAtLeastPoint x xNonnegative (suc n) =
  RP.≤-trans
    (originalLogFinitePartialAtLeastPoint x xNonnegative n)
    (Log.sourceLogPartialIncreasing x xNonnegative (suc n))

originalLogFinitePartialStrictlyPositive :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_ R.0ℝ
    (Finite.originalLogFinitePartial x (suc n))
originalLogFinitePartialStrictlyPositive x xPositive n =
  RP.<-≤-trans
    xPositive
    (originalLogFinitePartialAtLeastPoint
      x (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive)) n)

-- Original bounded positive exp factor at every finite positive
-- source partial: no monotonic-exp shortcut at an unselected value.
originalFiniteNegativeLogExpPositive :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_ R.0ℝ
    (Finite.originalNegativeLogFiniteExponential x (suc n))
originalFiniteNegativeLogExpPositive x xPositive n =
  NegativeExp.negativeExpPositive
    (originalLogFinitePartialStrictlyPositive x xPositive n)

originalFiniteNegativeLogExpBelowOne :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_
    (Finite.originalNegativeLogFiniteExponential x (suc n))
    R.1ℝ
originalFiniteNegativeLogExpBelowOne x xPositive n =
  NegativeExp.negativeExpBelowOne
    (originalLogFinitePartialStrictlyPositive x xPositive n)

-- Signed residual x^N F_N is nonnegative for source x>0.
originalFiniteNegativeLogExpResidualNonnegative :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R.NonNegative
    (R._*_
      (Finite.originalNegativeLogFiniteExponential x (suc n))
      (R.pow x (suc n)))
originalFiniteNegativeLogExpResidualNonnegative x xPositive n =
  RP.nonNegx,y⇒nonNegx*y
    (RP.0≤x⇒nonNegx
      (RP.<⇒≤ (originalFiniteNegativeLogExpPositive x xPositive n)))
    (Seq.nonNegx⇒nonNegxⁿ (suc n)
      (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive)))

-- The bound is UNIFORM in x: its only analytic scale is the
-- actual original Bishop power r^N, for one chosen 0<r<1.
originalFiniteNegativeLogExpUniformResidualBound :
  (radius x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (xInside : R._≤_ x radius) →
  (n : Nat) →
  R._≤_
    (R.∣ R._*_
      (Finite.originalNegativeLogFiniteExponential x (suc n))
      (R.pow x (suc n)) ∣)
    (R.pow radius (suc n))
originalFiniteNegativeLogExpUniformResidualBound
    radius x xPositive xInside n =
  let
    powNonnegative =
      Seq.nonNegx⇒nonNegxⁿ
        (suc n) (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
    expBelow =
      RP.<⇒≤ (originalFiniteNegativeLogExpBelowOne x xPositive n)
    boundExpByOne =
      RP.≤-respʳ-≃
        (RP.*-identityˡ (R.pow x (suc n)))
        (RP.*-monoʳ-≤-nonNeg
          expBelow powNonnegative)
    boundPower =
      Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
        (suc n) xInside
        (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
  in
  RP.≤-respˡ-≃
    (RP.nonNegx⇒∣x∣≃x
      (originalFiniteNegativeLogExpResidualNonnegative
        x xPositive n))
    (RP.≤-trans boundExpByOne boundPower)


------------------------------------------------------------------------
-- EFFECTIVE SHARED CUTOFF FOR ALL 0<x<=r<1.
-- This is a genuine, source-derived common modulus of the original
-- finite exponential-LOG differential residual. It pays the
-- uniformity missing from the earlier pointwise ODE residual.
------------------------------------------------------------------------

open import Data.Product.Base using (proj₁; proj₂)
import Data.Nat.Base as Nat using (NonZero; _≥_)
import Data.Nat.Properties as NatP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)

originalFiniteExpLogResidualCutoff :
  (radius : R.ℝ) →
  R._<_ (R.∣ radius ∣) R.1ℝ →
  (k : Nat) → .{{_ : Nat.NonZero k}} →
  Nat
originalFiniteExpLogResidualCutoff radius inside k =
  suc (proj₁
    (Seq.convergence-getter
      (R.0ℝ , Seq.∣r∣<1⇒rⁿ→0 inside)
      k))

originalFiniteExpLogUniformResidualSmall :
  (radius : R.ℝ) →
  (radiusInside : R._<_ (R.∣ radius ∣) R.1ℝ) →
  (k : Nat) → .{{_ : Nat.NonZero k}} →
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (xInside : R._≤_ x radius) →
  (n : Nat) →
  (suc n) Nat.≥
    originalFiniteExpLogResidualCutoff radius radiusInside k →
  R._≤_
    (R.∣ R._*_
      (Finite.originalNegativeLogFiniteExponential x (suc n))
      (R.pow x (suc n)) ∣)
    (R._⋆ (+ 1 / k))
originalFiniteExpLogUniformResidualSmall
    radius radiusInside k x xPositive xInside n pastCutoff =
  let
    rPower = R.pow radius (suc n)
    receipt = Seq.convergence-getter
      (R.0ℝ , Seq.∣r∣<1⇒rⁿ→0 radiusInside) k
    radiusError =
      proj₂ receipt (suc n) pastCutoff
    rPowerBelowAbsoluteError : R._≤_ rPower
      (R.∣ R._-_ rPower R.0ℝ ∣)
    rPowerBelowAbsoluteError =
      RP.≤-respʳ-≃
        (RP.∣-∣-cong
          (RP.≃-symm ((let open RP.ℝ-Solver in
           solve 1
             (λ value → value ⊖ Κ 0ℚᵘ ⊜ value)
             RP.≃-refl rPower))))
        (RP.x≤∣x∣ {x = rPower})
  in
  RP.≤-trans
    (originalFiniteNegativeLogExpUniformResidualBound
      radius x xPositive xInside n)
    (RP.≤-trans rPowerBelowAbsoluteError radiusError)
