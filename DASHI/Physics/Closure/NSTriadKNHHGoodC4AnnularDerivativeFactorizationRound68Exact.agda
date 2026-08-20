module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularDerivativeFactorizationRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 68 / FACTORED C4 TRANSITION DERIVATIVES
--
-- The degree-nine transition from Round67 has a much more informative
-- derivative structure than its expanded coefficients suggest.  Exactly:
--
--   S'(t)   = 630 t^4 (1-t)^4,
--   S''(t)  = 2520 t^3 (t-1)^3 (2t-1),
--   S'''(t) = 2520 t^2 (t-1)^2 (14t^2-14t+3),
--   S''''(t)=15120 t(t-1)(2t-1)(7t^2-7t+1).
--
-- These identities expose all endpoint vanishing factors and make later
-- derivative bounds on the compact annular transition a finite ordered-field
-- problem.  They are exact rational polynomial identities, not numerical
-- estimates or smoothness assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4

c3 c7 c14 c15120 c2520 c630 : ℚ
c3 = Int.+ 3 / 1
c7 = Int.+ 7 / 1
c14 = Int.+ 14 / 1
c15120 = Int.+ 15120 / 1
c2520 = Int.+ 2520 / 1
c630 = Int.+ 630 / 1

smoothStep4D1Factored : ∀ t →
  C4.smoothStep4D1 t
  ≡ c630 * C4.fourth t * C4.fourth (1ℚ - t)
smoothStep4D1Factored t = solve (t ∷ [])

smoothStep4D2Factored : ∀ t →
  C4.smoothStep4D2 t
  ≡ c2520 * C4.cube t * C4.cube (t - 1ℚ)
      * ((t + t) - 1ℚ)
smoothStep4D2Factored t = solve (t ∷ [])

smoothStep4D3Factored : ∀ t →
  C4.smoothStep4D3 t
  ≡ c2520 * C4.square t * C4.square (t - 1ℚ)
      * (c14 * C4.square t - c14 * t + c3)
smoothStep4D3Factored t = solve (t ∷ [])

smoothStep4D4Factored : ∀ t →
  C4.smoothStep4D4 t
  ≡ c15120 * t * (t - 1ℚ) * ((t + t) - 1ℚ)
      * (c7 * C4.square t - c7 * t + 1ℚ)
smoothStep4D4Factored t = solve (t ∷ [])

round68C4TransitionDerivativesFactored : Bool
round68C4TransitionDerivativesFactored = true

round68C4TransitionDerivativesFactoredIsTrue :
  round68C4TransitionDerivativesFactored ≡ true
round68C4TransitionDerivativesFactoredIsTrue = refl
