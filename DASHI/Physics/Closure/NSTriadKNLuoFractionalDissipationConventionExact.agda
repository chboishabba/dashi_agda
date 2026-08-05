module DASHI.Physics.Closure.NSTriadKNLuoFractionalDissipationConventionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Diego Córdoba; Luis Martínez-Zoroa; Fan Zheng.
-- Title: "Finite Time Blow-Up for the Hypodissipative Navier Stokes
-- Equations with a Force in L^1_t C_x^{1,epsilon} cap L^infinity_t L^2_x".
-- Archive for Rational Mechanics and Analysis 250 (2026), article 38.
-- DOI: 10.1007/s00205-026-02198-0.
-- arXiv DOI: 10.48550/arXiv.2407.06776.
--
-- PURPOSE
-- Prevent a consequential convention error.  The paper writes the
-- dissipative multiplier as
--
--   |nabla|^alpha = (-Delta)^(alpha/2),
--
-- so the classical Laplacian is alpha=2.  In the alternate convention
-- (-Delta)^s, the same operator has alpha=2s and the classical Laplacian is
-- s=1.  The conversion and both standard-Laplacian identifications are proved
-- exactly over the rationals.
--
-- The cited blow-up theorem covers alpha in [0,alpha_0), with
-- alpha_0=(22-8 sqrt(7))/9, not a perturbative interval just below alpha=2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

paperOrderFromFractionalPower : ℚ → ℚ
paperOrderFromFractionalPower s = two * s

fractionalPowerFromPaperOrder : ℚ → ℚ
fractionalPowerFromPaperOrder alpha = half * alpha

paperThenFractional :
  (s : ℚ) →
  fractionalPowerFromPaperOrder
    (paperOrderFromFractionalPower s)
  ≡ s
paperThenFractional s = solve (s ∷ [])

fractionalThenPaper :
  (alpha : ℚ) →
  paperOrderFromFractionalPower
    (fractionalPowerFromPaperOrder alpha)
  ≡ alpha
fractionalThenPaper alpha = solve (alpha ∷ [])

standardLaplacianFractionalPower : ℚ
standardLaplacianFractionalPower = Int.+ 1 / 1

standardLaplacianPaperOrder : ℚ
standardLaplacianPaperOrder = Int.+ 2 / 1

standardConventionAgreement :
  paperOrderFromFractionalPower standardLaplacianFractionalPower
  ≡ standardLaplacianPaperOrder
standardConventionAgreement = solve []

standardConventionAgreementReverse :
  fractionalPowerFromPaperOrder standardLaplacianPaperOrder
  ≡ standardLaplacianFractionalPower
standardConventionAgreementReverse = solve []
