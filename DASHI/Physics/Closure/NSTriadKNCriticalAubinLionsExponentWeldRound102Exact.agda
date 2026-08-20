module DASHI.Physics.Closure.NSTriadKNCriticalAubinLionsExponentWeldRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- Annali di Matematica Pura ed Applicata 146 (1987), 65--96.
-- DOI: 10.1007/BF01762360.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / CRITICAL AUBIN--LIONS EXPONENT WELD
--
-- Once a cutoff-uniform
--
--   L^infinity_t H^(1/2)  cap  L^2_t H^(3/2)
--
-- Galerkin barrier is available, the exponent bookkeeping needed for the
-- standard compactness passage is exact:
--
--   interpolation: theta=1/2 gives L^4_t H^1,
--   H^1(T^3) -> L^6,
--   H^(1/2)(T^3) -> L^3,
--   grad H^(3/2) -> H^(1/2) -> L^3,
--
-- and therefore
--
--   u in L^4_t L^6_x,
--   grad u in L^2_t L^3_x,
--   u.grad u in L^(4/3)_t L^2_x subset L^(4/3)_t H^(-1/2)_x.
--
-- Together with Delta u in L^2_t H^(-1/2), this gives the natural Simon
-- time-derivative exponent 4/3.  This file proves the rational exponent
-- identities; the actual Sobolev embeddings/compact inclusion remain the
-- standard analytic theorem instantiation, not new Clay dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

half quarter threeQuarters one third sixth threeHalves : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
threeQuarters = Int.+ 3 / 4
one = Int.+ 1 / 1
third = Int.+ 1 / 3
sixth = Int.+ 1 / 6
threeHalves = Int.+ 3 / 2

-- Interpolating L^infinity and L^2 with theta=1/2 gives L^4.
timeInterpolationReciprocalIdentity :
  half * half ≡ quarter
timeInterpolationReciprocalIdentity = solve []

-- The same theta sends H^(1/2), H^(3/2) to H^1.
spaceInterpolationCriticalIdentity :
  half * half + half * threeHalves ≡ one
spaceInterpolationCriticalIdentity = solve []

-- Holder in time: L^4 * L^2 -> L^(4/3).
nonlinearTimeHolderIdentity :
  quarter + half ≡ threeQuarters
nonlinearTimeHolderIdentity = solve []

-- Holder in space: L^6 * L^3 -> L^2.
nonlinearSpaceHolderIdentity :
  sixth + third ≡ half
nonlinearSpaceHolderIdentity = solve []

-- Serrin endpoint: 2/4 + 3/6 = 1.
serrinCriticalIdentity :
  half + half ≡ one
serrinCriticalIdentity = solve []

round102CriticalAubinLionsExponentArithmeticClosed : Bool
round102CriticalAubinLionsExponentArithmeticClosed = true

round102CriticalAubinLionsExponentArithmeticClosedIsTrue :
  round102CriticalAubinLionsExponentArithmeticClosed ≡ true
round102CriticalAubinLionsExponentArithmeticClosedIsTrue = refl
