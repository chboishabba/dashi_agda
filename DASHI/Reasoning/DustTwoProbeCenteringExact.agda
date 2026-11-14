module DASHI.Reasoning.DustTwoProbeCenteringExact where

-- SOURCE ATTRIBUTION
-- Dust original activation perturbation: Dahal, Mandal,
-- Gülbahar, Vegesna (2026). The elementary sample-centering
-- algebra here is DASHI-derived; it is NOT a paper claim.
--
-- This proves a mathematical special case of population-centred
-- forward-only credit. Not an unbiased-general-gradient theorem.
-- No new Walsh carrier: see existing YM Walsh #575.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

half : ℚ
half = + 1 / 2

quarter : ℚ
quarter = + 1 / 4

meanTwo : ℚ → ℚ → ℚ
meanTwo a b = half * (a + b)

centeredTwoCredit : ℚ → ℚ → ℚ
centeredTwoCredit a b =
  half * (((a + - (meanTwo a b)) * a) +
          ((b + - (meanTwo a b)) * b))

-- For two arbitrary rational draws, sample-mean centering is a
-- nonnegative square up to the 1/4 factor.
twoProbeCenteredSquare :
  (a b : ℚ) →
  centeredTwoCredit a b
    ≡ quarter * ((a + - b) * (a + - b))
twoProbeCenteredSquare a b = ℚRing.solve-∀ a b

-- Equal perturbations yield ZERO estimated credit, independently
-- of the true affine loss gradient. This is a useful obstruction:
-- two draws are not sufficient if their directions coincide.
identicalProbesCancel : (a : ℚ) →
  centeredTwoCredit a a ≡ 0ℚ
identicalProbesCancel a = ℚRing.solve-∀ a

-- Balanced antithetic probes ±1 have exact unit covariance,
-- rather than the iid finite-K expected factor of 1/2.
antitheticPairUnitCredit :
  centeredTwoCredit 1ℚ (- 1ℚ) ≡ 1ℚ
antitheticPairUnitCredit = ℚRing.solve-∀

-- This is the distinction between dependent designed probes and
-- independent samples; never apply the iid (K-1)/K result here.


-- Apply the exact two-probe covariance factor to an arbitrary affine
-- loss slope g. This is still a deterministic two-draw result, not a
-- probability or convergence statement.
twoProbeAffineCredit : ℚ → ℚ → ℚ → ℚ
twoProbeAffineCredit g a b = g * centeredTwoCredit a b

twoProbeAffineSquare :
  (g a b : ℚ) →
  twoProbeAffineCredit g a b
    ≡ g * quarter * ((a + - b) * (a + - b))
twoProbeAffineSquare g a b = ℚRing.solve-∀ g a b

twoProbeAffineIdentical :
  (g a : ℚ) →
  twoProbeAffineCredit g a a ≡ 0ℚ
twoProbeAffineIdentical g a = ℚRing.solve-∀ g a

twoProbeAffineAntithetic :
  (g : ℚ) →
  twoProbeAffineCredit g 1ℚ (- 1ℚ) ≡ g
twoProbeAffineAntithetic g = ℚRing.solve-∀ g
