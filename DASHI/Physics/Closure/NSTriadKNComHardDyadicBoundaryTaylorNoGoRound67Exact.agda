module DASHI.Physics.Closure.NSTriadKNComHardDyadicBoundaryTaylorNoGoRound67Exact where

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
-- ROUND 67 / B-E HARD-CUTOFF FALSIFIER
--
-- A Taylor estimate cannot be taken on the hard shell indicator itself.  The
-- obstruction already occurs in one radial lattice coordinate.  `hardPrefix`
-- is the exact characteristic function of the integer prefix {0,...,N}.  At
-- every boundary N it has
--
--      hardPrefix N N       = 1
--      hardPrefix N (N + 1) = 0.
--
-- Hence a displacement of one lattice unit produces an order-one multiplier
-- jump at arbitrarily large N.  Specializing N to the literal dyadic radius
-- 2^shell gives a hard boundary counterexample at every shell scale.
--
-- This does not reject the hard projector for exact Fourier bookkeeping.  It
-- rejects only the false inference
--
--      low displacement / high frequency  => small hard-projector difference.
--
-- Round67 must therefore Taylor-expand a smooth annular cutoff and separately
-- identify its lattice restriction with the intended localized operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)

import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

hardPrefix : Nat → Nat → ℚ
hardPrefix zero zero = 1ℚ
hardPrefix zero (suc value) = 0ℚ
hardPrefix (suc boundary) zero = 1ℚ
hardPrefix (suc boundary) (suc value) = hardPrefix boundary value

hardPrefixAtBoundaryIsOne : ∀ boundary →
  hardPrefix boundary boundary ≡ 1ℚ
hardPrefixAtBoundaryIsOne zero = refl
hardPrefixAtBoundaryIsOne (suc boundary) =
  hardPrefixAtBoundaryIsOne boundary

hardPrefixImmediatelyOutsideIsZero : ∀ boundary →
  hardPrefix boundary (suc boundary) ≡ 0ℚ
hardPrefixImmediatelyOutsideIsZero zero = refl
hardPrefixImmediatelyOutsideIsZero (suc boundary) =
  hardPrefixImmediatelyOutsideIsZero boundary

record UnitHardBoundaryJump (boundary : Nat) : Set where
  field
    insideValue : hardPrefix boundary boundary ≡ 1ℚ
    outsideValue : hardPrefix boundary (suc boundary) ≡ 0ℚ

open UnitHardBoundaryJump public

unitHardBoundaryJump : ∀ boundary → UnitHardBoundaryJump boundary
unitHardBoundaryJump boundary = record
  { insideValue = hardPrefixAtBoundaryIsOne boundary
  ; outsideValue = hardPrefixImmediatelyOutsideIsZero boundary
  }

dyadicHardBoundaryJump : ∀ shell →
  UnitHardBoundaryJump (Shell.pow2 shell)
dyadicHardBoundaryJump shell = unitHardBoundaryJump (Shell.pow2 shell)

round67HardProjectorTaylorRouteRuledOut : Bool
round67HardProjectorTaylorRouteRuledOut = true

round67HardProjectorStillAllowedForBookkeeping : Bool
round67HardProjectorStillAllowedForBookkeeping = true

round67HardProjectorTaylorRouteRuledOutIsTrue :
  round67HardProjectorTaylorRouteRuledOut ≡ true
round67HardProjectorTaylorRouteRuledOutIsTrue = refl

round67HardProjectorStillAllowedForBookkeepingIsTrue :
  round67HardProjectorStillAllowedForBookkeeping ≡ true
round67HardProjectorStillAllowedForBookkeepingIsTrue = refl
