module DASHI.Physics.Closure.NSTriadKNEigenpacketRecombinationCounterexampleRound101Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND101 / SHARP RECOMBINATION FALSIFIER
--
-- Round100's exact-radius identity can hold with ZERO relative-growth
-- numerator on every individual eigenspace while the union has STRICTLY
-- POSITIVE relative growth.  Hence an estimate proved independently on every
-- exact eigenspace cannot be recombined by Parseval alone.
--
-- Take two cells
--
--   lambda1=1, E1=1, q1=1, qdot1=2,
--   lambda2=2, E2=1, q2=0, qdot2=0.
--
-- Each diagonal numerator is exactly
--
--   lambda_i (E_i qdot_i - 2 q_i^2) = 0.
--
-- But after recombination
--
--   E=2, q=1, qdot=2,
--   D=lambda1 E1 + lambda2 E2 = 3,
--   Ddot=2(lambda1 q1 + lambda2 q2)=2,
--
-- and therefore
--
--   qdot D - q Ddot = 2*3 - 1*2 = 4 > 0.
--
-- This isolates the cross-radius defect without any lattice counting,
-- cardinality, or PDE assumption.  Any viable eigenpacket route must control
-- this defect BEFORE claiming dyadic/critical recombination.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open ℚP using (_<?_)
import Data.Integer.Base as Int

lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 : ℚ
lambda1 = 1ℚ
lambda2 = Int.+ 2 / 1
E1 = 1ℚ
E2 = 1ℚ
q1 = 1ℚ
q2 = 0ℚ
qdot1 = Int.+ 2 / 1
qdot2 = 0ℚ

diagonalNumerator : ℚ → ℚ → ℚ → ℚ → ℚ
diagonalNumerator lambda E q qdot =
  lambda * (E * qdot - (Int.+ 2 / 1) * (q * q))

recombinedNumerator :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
recombinedNumerator l1 l2 e1 e2 a b da db =
  (da + db) * (l1 * e1 + l2 * e2)
    - (a + b) * ((Int.+ 2 / 1) * (l1 * a + l2 * b))

firstDiagonalNumeratorZero :
  diagonalNumerator lambda1 E1 q1 qdot1 ≡ 0ℚ
firstDiagonalNumeratorZero = solve []

secondDiagonalNumeratorZero :
  diagonalNumerator lambda2 E2 q2 qdot2 ≡ 0ℚ
secondDiagonalNumeratorZero = solve []

recombinedNumeratorIsFour :
  recombinedNumerator lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
  ≡ Int.+ 4 / 1
recombinedNumeratorIsFour = solve []

recombinedNumeratorStrictlyPositive :
  0ℚ < recombinedNumerator lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
recombinedNumeratorStrictlyPositive
  rewrite recombinedNumeratorIsFour =
  toWitness {a? = 0ℚ <? (Int.+ 4 / 1)} _

round101EveryDiagonalEigenpacketNumeratorCanVanish : Bool
round101EveryDiagonalEigenpacketNumeratorCanVanish = true

round101RecombinedNumeratorCanStillBeStrictlyPositive : Bool
round101RecombinedNumeratorCanStillBeStrictlyPositive = true

round101DiagonalEigenpacketControlAloneImpliesShellControl : Bool
round101DiagonalEigenpacketControlAloneImpliesShellControl = false

round101DiagonalEigenpacketControlAloneImpliesShellControlIsFalse :
  round101DiagonalEigenpacketControlAloneImpliesShellControl ≡ false
round101DiagonalEigenpacketControlAloneImpliesShellControlIsFalse = refl
