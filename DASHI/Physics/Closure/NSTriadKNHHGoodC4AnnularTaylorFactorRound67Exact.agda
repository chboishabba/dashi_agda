module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularTaylorFactorRound67Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 67 / CONCRETE SECOND-ORDER TAYLOR FACTOR
--
-- For the explicit fourth-order smoothstep S constructed in Round67, prove
-- algebraically -- not analytically imported -- that
--
--   S(x+h) = S(x) + S'(x) h + h^2 Q(x,h)
--
-- for an explicit rational polynomial Q.  Therefore the exact Frechet
-- remainder from the companion bridge is divisible by h^2 on the nose.
--
-- This is the concrete higher-order small parameter that the hard shell
-- indicator cannot possess.  Quantitative B3 still has to relate the physical
-- radial displacement to the dyadic low/dominant ratio and combine this scalar
-- cutoff factor with derivatives of the angular strain multiplier, but the
-- cutoff's second-order Taylor structure itself is now constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularFrechetBridgeRound67Exact as FrechetBridge

c1260 c5880 c6300 c8400 c8820 c11340 c18900 c22050 : ℚ
c1260 = Int.+ 1260 / 1
c5880 = Int.+ 5880 / 1
c6300 = Int.+ 6300 / 1
c8400 = Int.+ 8400 / 1
c8820 = Int.+ 8820 / 1
c11340 = Int.+ 11340 / 1
c18900 = Int.+ 18900 / 1
c22050 = Int.+ 22050 / 1

taylorQuadraticCoefficient : ℚ → ℚ → ℚ
taylorQuadraticCoefficient x h =
    C4.c70 * C4.seventh h
  + C4.sixth h * (C4.c630 * x + (- C4.c315))
  + C4.fifth h
      * (C4.c2520 * C4.square x
        + (- (C4.c2520 * x))
        + C4.c540)
  + C4.fourth h
      * (c5880 * C4.cube x
        + (- (c8820 * C4.square x))
        + C4.c3780 * x
        + (- C4.c420))
  + C4.cube h
      * (c8820 * C4.fourth x
        + (- (C4.c17640 * C4.cube x))
        + c11340 * C4.square x
        + (- (C4.c2520 * x))
        + C4.c126)
  + C4.square h
      * (c8820 * C4.fifth x
        + (- (c22050 * C4.fourth x))
        + c18900 * C4.cube x
        + (- (c6300 * C4.square x))
        + C4.c630 * x)
  + h
      * (c5880 * C4.sixth x
        + (- (C4.c17640 * C4.fifth x))
        + c18900 * C4.fourth x
        + (- (c8400 * C4.cube x))
        + c1260 * C4.square x)
  + (C4.c2520 * C4.seventh x
      + (- (c8820 * C4.sixth x))
      + c11340 * C4.fifth x
      + (- (c6300 * C4.fourth x))
      + c1260 * C4.cube x)

smoothStep4SecondOrderTaylorExact : ∀ x h →
  C4.smoothStep4 (x + h)
  ≡ C4.smoothStep4 x
      + (C4.smoothStep4D1 x * h
        + (h * h) * taylorQuadraticCoefficient x h)
smoothStep4SecondOrderTaylorExact x h =
  solve (x ∷ h ∷ [])

smoothStep4RemainderHasExactSquareFactor : ∀ x h →
  FrechetBridge.smoothStep4ExactRemainder x h
  ≡ (h * h) * taylorQuadraticCoefficient x h
smoothStep4RemainderHasExactSquareFactor x h =
  solve (x ∷ h ∷ [])

round67ExplicitAnnularTaylorSquareFactorConstructed : Bool
round67ExplicitAnnularTaylorSquareFactorConstructed = true

round67ExplicitAnnularTaylorSquareFactorConstructedIsTrue :
  round67ExplicitAnnularTaylorSquareFactorConstructed ≡ true
round67ExplicitAnnularTaylorSquareFactorConstructedIsTrue = refl
