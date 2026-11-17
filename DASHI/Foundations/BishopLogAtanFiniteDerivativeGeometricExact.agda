{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact where

------------------------------------------------------------------------
-- Shared ORIGINAL Bishop polynomial telescope for LOG and ATAN.
--
-- This is a genuine ALL-N proof on the vendored Real.ℝ, not a
-- postulated power-series differentiation theorem and not a finite
-- numerical test.
--
-- For P_N(q) = sum_(k<N) q^k, exactly:
--       (1-q) P_N(q) ~= 1-q^N.
--
-- The LOG derivative partial is P_N(x), and the ATAN derivative
-- partial is P_N(-x*x), so exactly:
--
--       (1-x) P_N(x) ~= 1-x^N,
--       (1+x*x) P_N(-x*x) ~= 1-(-x*x)^N.
--
-- These are the precise finite residuals for the ORIGINAL Bishop
-- negative-log and arctangent power series, respectively. To use
-- them analytically one must prove (a) the finite derivatives are
-- those of the literal source partial sums, (b) uniform derivative
-- convergence on compact sub-half-balls, and (c) derivative-limit
-- interchange. This module does not assume any of those results.
--
-- Source: pinned vendor/bishop Real, RealProperties; elementary
-- constructive geometric telescoping.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as R
import RealProperties as RP

geometricPartial : R.ℝ → Nat → R.ℝ
geometricPartial q zero = R.0ℝ
geometricPartial q (suc n) =
  R._+_ (geometricPartial q n) (R.pow q n)

geometricPolynomialTelescope :
  (q : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_ (R._-_ R.1ℝ q) (geometricPartial q n))
    (R._-_ R.1ℝ (R.pow q n))
geometricPolynomialTelescope q zero =
  let open RP.ℝ-Solver
  in solve 1
    (λ q′ →
      (Κ 1ℚᵘ ⊖ q′) ⊗ Κ 0ℚᵘ
      ⊜ Κ 1ℚᵘ ⊖ Κ 1ℚᵘ)
    RP.≃-refl q
geometricPolynomialTelescope q (suc n) =
  let
    partial = geometricPartial q n
    last = R.pow q n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 3
      (λ q′ s p →
        (Κ 1ℚᵘ ⊖ q′) ⊗ (s ⊕ p)
        ⊜ ((Κ 1ℚᵘ ⊖ q′) ⊗ s)
          ⊕ (p ⊖ (p ⊗ q′)))
      RP.≃-refl q partial last)
    (RP.≃-trans
      (RP.+-cong
        (geometricPolynomialTelescope q n)
        RP.≃-refl)
      (solve 2
        (λ q′ p →
          (Κ 1ℚᵘ ⊖ p) ⊕ (p ⊖ (p ⊗ q′))
          ⊜ Κ 1ℚᵘ ⊖ (p ⊗ q′))
        RP.≃-refl q last))

-- This *literal* polynomial is the derivative of the first N
-- nonzero coefficients of the negative-log original source.
negativeLogDerivativePolynomial : R.ℝ → Nat → R.ℝ
negativeLogDerivativePolynomial = geometricPartial

negativeLogDerivativeFiniteResidual :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_ (R._-_ R.1ℝ x)
      (negativeLogDerivativePolynomial x n))
    (R._-_ R.1ℝ (R.pow x n))
negativeLogDerivativeFiniteResidual =
  geometricPolynomialTelescope

-- This *literal* polynomial has the coefficients of the derivative
-- of the first N original alternating atan terms.
arctanDerivativePolynomial : R.ℝ → Nat → R.ℝ
arctanDerivativePolynomial x n =
  geometricPartial (R.-_ (R._*_ x x)) n

arctanDerivativeFiniteResidual :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_
      (R._+_ R.1ℝ (R._*_ x x))
      (arctanDerivativePolynomial x n))
    (R._-_
      R.1ℝ
      (R.pow (R.-_ (R._*_ x x)) n))
arctanDerivativeFiniteResidual x n =
  let
    q = R.-_ (R._*_ x x)
    factor :
      R._≃_
        (R._+_ R.1ℝ (R._*_ x x))
        (R._-_ R.1ℝ q)
    factor =
      let open RP.ℝ-Solver
      in solve 1
        (λ y →
          Κ 1ℚᵘ ⊕ y ⊜ Κ 1ℚᵘ ⊖ (⊝ y))
        RP.≃-refl (R._*_ x x)
  in
  RP.≃-trans
    (RP.*-cong factor RP.≃-refl)
    (geometricPolynomialTelescope q n)
