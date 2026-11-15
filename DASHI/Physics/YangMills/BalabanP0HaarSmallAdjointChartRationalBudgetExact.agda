{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanP0HaarSmallAdjointChartRationalBudgetExact where

------------------------------------------------------------------------
-- BAŁABAN L1 / P0: SOURCE-INDEPENDENT EXACT RATIONAL HAAR TAIL BUDGET
--
-- For |r| <= 1, the STANDARD Euler sine product and zeta integral
-- comparison imply
--
--   0 <= -2 log(sin(r/2)/(r/2)) - r^2/12 - r^4/1440
--     <= r^6 / 56700.
--
-- For a compact semisimple adjoint X with eigenvalue pairs ±i lambda_j,
-- |lambda_j| <= rho <= 1 and -tr(ad_X^2) = C_A ||X||^2,
--
--   0 <= -log J_exp(X) - (C_A/24) ||X||^2
--      <= (323/907200) C_A rho^2 ||X||^2.
--
-- The ANALYTIC product/logarithm inequality and the spectral/Jacobian
-- identification are not proved in this Agda module. It proves only the
-- EXACT RATIONAL BUDGET used by that independent analysis. In particular
-- it neither supplies the Bałaban physical chart nor cutoff-uniform
-- Wilson/FP/Haar remainders.
--
-- Independent derivation and reproducible arithmetic check:
-- Docs/roadmaps/BalabanL1AdjointHaarLocalAnalyticTail20261113.md
-- scripts/check_balaban_l1_adjoint_haar_local_tail.py
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

haarQuarticCoefficient : ℚ
haarQuarticCoefficient = + 1 / 1440

haarSixthOrderTailMajorant : ℚ
haarSixthOrderTailMajorant = + 1 / 56700

haarFourthOrderResidualBudget : ℚ
haarFourthOrderResidualBudget = + 323 / 453600

haarAdjointCasimirResidualBudget : ℚ
haarAdjointCasimirResidualBudget = + 323 / 907200

haarFourthAndHigherBudgetExact :
  haarQuarticCoefficient + haarSixthOrderTailMajorant
    ≡ haarFourthOrderResidualBudget
haarFourthAndHigherBudgetExact = ℚRing.solve-∀

haarPairToAdjointCasimirBudgetExact :
  haarFourthOrderResidualBudget * (+ 1 / 2)
    ≡ haarAdjointCasimirResidualBudget
haarPairToAdjointCasimirBudgetExact = ℚRing.solve-∀
