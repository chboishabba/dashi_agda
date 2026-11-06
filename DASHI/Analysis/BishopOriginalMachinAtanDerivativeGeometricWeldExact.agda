{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalMachinAtanDerivativeGeometricWeldExact where

------------------------------------------------------------------------
-- K05-PI: THE ACTUAL ORIGINAL MACHIN ATAN FINITE DERIVATIVE IS
-- EXACTLY THE GEOMETRIC POLYNOMIAL IN THE VENDORED BISHOP REAL.
--
-- Original atan term derivative proved in
-- BishopOriginalMachinAtanFiniteDerivativeExact:
--     (-1)^n * x^(2n).
-- This module proves for *all* Nat n on the ORIGINAL setoid:
--     (-1)^n * x^(2n) ~= (-x*x)^n.
--
-- Hence every actual finite source atan partial P_N has a
-- BishopFactorDerivativeAt whose derivative is precisely
--     geometricPartial(-x*x,N),
-- and the exact finite residual equation
--     (1+x*x) P'_N(x) ~= 1-(-x*x)^N
-- is immediately inherited from the original geometric owner.
--
-- No derivative-interchange axiom is hidden: the infinite-limit
-- derivative still needs a uniform quotient/tail certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Sign
import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as Original
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates

originalAtanDerivedTermIsGeometricCoefficient :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (Original.sourceAtanDerivativeTerm x n)
    (R.pow (R.-_ (R._*_ x x)) n)
originalAtanDerivedTermIsGeometricCoefficient x zero =
  let open RP.ℝ-Solver in
  solve 0
    (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
    RP.≃-refl
originalAtanDerivedTermIsGeometricCoefficient x (suc n) =
  let
    sign = Terms.alternatingSign n
    p = R.pow x (Estimates.evenExponent n)
    square = R._*_ x x
    q = R.-_ square
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong
      (Sign.alternatingSignSuccessor n)
      RP.≃-refl)
    (RP.≃-trans
      (solve 3
        (λ sign′ p′ x′ →
          (⊝ sign′) ⊗ ((p′ ⊗ x′) ⊗ x′)
          ⊜ (sign′ ⊗ p′) ⊗ (⊝ (x′ ⊗ x′)))
        RP.≃-refl sign p x)
      (RP.*-cong
        (originalAtanDerivedTermIsGeometricCoefficient x n)
        RP.≃-refl))

originalAtanFiniteDerivedSumIsGeometricPartial :
  (x : R.ℝ) (count : Nat) →
  R._≃_
    (Original.sourceAtanDerivativeFinitePartial x count)
    (Geo.arctanDerivativePolynomial x count)
originalAtanFiniteDerivedSumIsGeometricPartial x zero =
  RP.≃-refl
originalAtanFiniteDerivedSumIsGeometricPartial x (suc count) =
  RP.+-cong
    (originalAtanFiniteDerivedSumIsGeometricPartial x count)
    (originalAtanDerivedTermIsGeometricCoefficient x count)

originalAtanFinitePartialNativeGeometricDerivative :
  (x : R.ℝ) (count : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → Original.sourceAtanFinitePartial y count)
    x
    (Geo.arctanDerivativePolynomial x count)
originalAtanFinitePartialNativeGeometricDerivative x count =
  Factor.factorDerivativeCongruence
    (λ _ → RP.≃-refl)
    (originalAtanFiniteDerivedSumIsGeometricPartial x count)
    (Original.originalMachinAtanFinitePartialFactorDerivative x count)

originalAtanFiniteNativeDerivativeResidual :
  (x : R.ℝ) (count : Nat) →
  R._≃_
    (R._*_
      (R._+_ R.1ℝ (R._*_ x x))
      (Geo.arctanDerivativePolynomial x count))
    (R._-_ R.1ℝ
      (R.pow (R.-_ (R._*_ x x)) count))
originalAtanFiniteNativeDerivativeResidual =
  Geo.arctanDerivativeFiniteResidual
