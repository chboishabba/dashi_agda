module DASHI.Physics.Closure.NSTriadKNComSameShellGradingCancellationNoGoRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Audit the tempting Round-49 shortcut that the d=0 Com channel might vanish
-- from P/Q odd grading or skew-adjointness alone. It does not. On the exact
-- two-channel carrier choose the skew off-diagonal transport
--
--        [ 0   1 ]
--   T =  [       ].
--        [ -1  0 ]
--
-- It is purely odd and skew-adjoint, yet [P,T](0,1)=(1,0) and its squared
-- norm is exactly 1. Any improvement of the same-shell 17/64 target must use
-- additional Fourier/shell structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ; 1ℚ; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ
import DASHI.Physics.Closure.NSTriadKNComAdjointCollapseRound40Exact as Adjoint

sameShellSkewOddTransport : PQ.LinearTransport2
sameShellSkewOddTransport =
  PQ.linear-transport2 0ℚ 1ℚ (- 1ℚ) 0ℚ

sameShellTransportIsSkewAdjoint :
  Adjoint.SkewAdjointTransport2 sameShellSkewOddTransport
sameShellTransportIsSkewAdjoint =
  Adjoint.skew-adjoint-transport2 refl

sameShellOddCommutatorOnFineBasis :
  PQ.commutator sameShellSkewOddTransport PQ.fineBasis
  ≡ PQ.split-state 1ℚ 0ℚ
sameShellOddCommutatorOnFineBasis =
  PQ.stateExt (solve []) (solve [])

sameShellOddCommutatorNormSquaredOne :
  PQ.stateNormSquared
    (PQ.commutator sameShellSkewOddTransport PQ.fineBasis)
  ≡ 1ℚ
sameShellOddCommutatorNormSquaredOne
  rewrite sameShellOddCommutatorOnFineBasis = solve []

sameShellCancellationNotForcedByGradingAndSkew : Bool
sameShellCancellationNotForcedByGradingAndSkew = true

sameShellCancellationNotForcedByGradingAndSkewIsTrue :
  sameShellCancellationNotForcedByGradingAndSkew ≡ true
sameShellCancellationNotForcedByGradingAndSkewIsTrue = refl
