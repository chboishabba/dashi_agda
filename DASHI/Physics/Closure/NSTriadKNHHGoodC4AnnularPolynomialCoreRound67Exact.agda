module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact where

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
-- ROUND 67 / E1 CONCRETE SMOOTH CUTOFF CORE
--
-- The hard shell indicator is retained for exact lattice bookkeeping but is
-- unsuitable for Taylor estimates.  Here we construct an explicit polynomial
-- transition with four vanishing boundary derivatives:
--
--   S(t) = 126 t^5 - 420 t^6 + 540 t^7 - 315 t^8 + 70 t^9.
--
-- It satisfies S(0)=0, S(1)=1 and S^(j)(0)=S^(j)(1)=0 for j=1,2,3,4.
-- These are exactly the gluing jets needed for a piecewise-zero/one annular
-- cutoff to have a C^4 boundary once the repository's continuum derivative
-- carrier is attached.  Unlike Round48's scale-invariant cutoff, this object
-- is deliberately non-homogeneous in the radial transition coordinate.
--
-- The polynomial identities below are exact over Q; there is no numerical
-- approximation or receipt field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

c70 c126 c315 c420 c540 c630 c2520 c3780 c5040 c7560 c12600 c15120 c17640 c22680 c35280 c50400 c105840 c113400 c151200 c211680 c453600 c529200 : ℚ
c70 = Int.+ 70 / 1
c126 = Int.+ 126 / 1
c315 = Int.+ 315 / 1
c420 = Int.+ 420 / 1
c540 = Int.+ 540 / 1
c630 = Int.+ 630 / 1
c2520 = Int.+ 2520 / 1
c3780 = Int.+ 3780 / 1
c5040 = Int.+ 5040 / 1
c7560 = Int.+ 7560 / 1
c12600 = Int.+ 12600 / 1
c15120 = Int.+ 15120 / 1
c17640 = Int.+ 17640 / 1
c22680 = Int.+ 22680 / 1
c35280 = Int.+ 35280 / 1
c50400 = Int.+ 50400 / 1
c105840 = Int.+ 105840 / 1
c113400 = Int.+ 113400 / 1
c151200 = Int.+ 151200 / 1
c211680 = Int.+ 211680 / 1
c453600 = Int.+ 453600 / 1
c529200 = Int.+ 529200 / 1

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = square x * x

fourth : ℚ → ℚ
fourth x = square x * square x

fifth : ℚ → ℚ
fifth x = fourth x * x

sixth : ℚ → ℚ
sixth x = fifth x * x

seventh : ℚ → ℚ
seventh x = sixth x * x

eighth : ℚ → ℚ
eighth x = seventh x * x

ninth : ℚ → ℚ
ninth x = eighth x * x

smoothStep4 : ℚ → ℚ
smoothStep4 t =
  c126 * fifth t
  + (- (c420 * sixth t))
  + c540 * seventh t
  + (- (c315 * eighth t))
  + c70 * ninth t

smoothStep4D1 : ℚ → ℚ
smoothStep4D1 t =
  c630 * fourth t
  + (- (c2520 * fifth t))
  + c3780 * sixth t
  + (- (c2520 * seventh t))
  + c630 * eighth t

smoothStep4D2 : ℚ → ℚ
smoothStep4D2 t =
  c2520 * cube t
  + (- (c12600 * fourth t))
  + c22680 * fifth t
  + (- (c17640 * sixth t))
  + c5040 * seventh t

smoothStep4D3 : ℚ → ℚ
smoothStep4D3 t =
  c7560 * square t
  + (- (c50400 * cube t))
  + c113400 * fourth t
  + (- (c105840 * fifth t))
  + c35280 * sixth t

smoothStep4D4 : ℚ → ℚ
smoothStep4D4 t =
  c15120 * t
  + (- (c151200 * square t))
  + c453600 * cube t
  + (- (c529200 * fourth t))
  + c211680 * fifth t

smoothStep4AtZero : smoothStep4 0ℚ ≡ 0ℚ
smoothStep4AtZero = solve []

smoothStep4AtOne : smoothStep4 1ℚ ≡ 1ℚ
smoothStep4AtOne = solve []

smoothStep4D1AtZero : smoothStep4D1 0ℚ ≡ 0ℚ
smoothStep4D1AtZero = solve []

smoothStep4D1AtOne : smoothStep4D1 1ℚ ≡ 0ℚ
smoothStep4D1AtOne = solve []

smoothStep4D2AtZero : smoothStep4D2 0ℚ ≡ 0ℚ
smoothStep4D2AtZero = solve []

smoothStep4D2AtOne : smoothStep4D2 1ℚ ≡ 0ℚ
smoothStep4D2AtOne = solve []

smoothStep4D3AtZero : smoothStep4D3 0ℚ ≡ 0ℚ
smoothStep4D3AtZero = solve []

smoothStep4D3AtOne : smoothStep4D3 1ℚ ≡ 0ℚ
smoothStep4D3AtOne = solve []

smoothStep4D4AtZero : smoothStep4D4 0ℚ ≡ 0ℚ
smoothStep4D4AtZero = solve []

smoothStep4D4AtOne : smoothStep4D4 1ℚ ≡ 0ℚ
smoothStep4D4AtOne = solve []

record FourthOrderTransitionJets : Set where
  field
    leftValue : smoothStep4 0ℚ ≡ 0ℚ
    rightValue : smoothStep4 1ℚ ≡ 1ℚ
    leftD1 : smoothStep4D1 0ℚ ≡ 0ℚ
    rightD1 : smoothStep4D1 1ℚ ≡ 0ℚ
    leftD2 : smoothStep4D2 0ℚ ≡ 0ℚ
    rightD2 : smoothStep4D2 1ℚ ≡ 0ℚ
    leftD3 : smoothStep4D3 0ℚ ≡ 0ℚ
    rightD3 : smoothStep4D3 1ℚ ≡ 0ℚ
    leftD4 : smoothStep4D4 0ℚ ≡ 0ℚ
    rightD4 : smoothStep4D4 1ℚ ≡ 0ℚ

open FourthOrderTransitionJets public

explicitFourthOrderTransitionJets : FourthOrderTransitionJets
explicitFourthOrderTransitionJets = record
  { leftValue = smoothStep4AtZero
  ; rightValue = smoothStep4AtOne
  ; leftD1 = smoothStep4D1AtZero
  ; rightD1 = smoothStep4D1AtOne
  ; leftD2 = smoothStep4D2AtZero
  ; rightD2 = smoothStep4D2AtOne
  ; leftD3 = smoothStep4D3AtZero
  ; rightD3 = smoothStep4D3AtOne
  ; leftD4 = smoothStep4D4AtZero
  ; rightD4 = smoothStep4D4AtOne
  }

round67ExplicitFourthOrderAnnularTransitionCoreConstructed : Bool
round67ExplicitFourthOrderAnnularTransitionCoreConstructed = true

round67ExplicitFourthOrderAnnularTransitionCoreConstructedIsTrue :
  round67ExplicitFourthOrderAnnularTransitionCoreConstructed ≡ true
round67ExplicitFourthOrderAnnularTransitionCoreConstructedIsTrue = refl
