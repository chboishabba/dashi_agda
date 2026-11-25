module DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact where

-- Source-written, not kernel checked. Exact original prefix edge identities.
-- No positivity or infinite analytic conclusion inferred from ring algebra.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; 1ℤ; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
import Data.Integer.Base as Z
import Agda.Builtin.Nat as N
import DASHI.Foundations.HypergeometricBSplitIntegerMergeExact as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH

P Q T : Nat → ℤ
P n = S.P (CH.sourcePrefix n)
Q n = S.Q (CH.sourcePrefix n)
T n = S.T (CH.sourcePrefix n)

a : Nat → ℤ
a n = Z.+_ (N._+_ CH.A (N._*_ CH.B n))

delta : Nat → ℤ
delta n = P n * CH.sourceP n * a n

prefixBOne : (n : Nat) → S.B (CH.sourcePrefix n) ≡ 1ℤ
prefixBOne zero = refl
prefixBOne (suc n) rewrite prefixBOne n = refl

prefixPStep : (n : Nat) → P (suc n) ≡ P n * CH.sourceP n
prefixPStep n = refl

prefixQStep : (n : Nat) → Q (suc n) ≡ Q n * CH.sourceQ n
prefixQStep n = refl

prefixTStep : (n : Nat) →
  T (suc n) ≡ T n * CH.sourceQ n + delta n
prefixTStep n rewrite prefixBOne n =
  solve 5
    (λ t q p u v →
      ((t :* q :* con 1ℤ) :+ (p :* con 1ℤ :* (v :* u)))
      := ((t :* q) :+ (p :* u :* v)))
    refl (T n) (CH.sourceQ n) (P n) (CH.sourceP n) (a n)

-- Denominator-cleared finite sum transport, no division by zero.
-- Positive Q proofs and rational embedding remain explicit separate work.
sourceAdjacentCrossIdentity : (n : Nat) →
  T (suc n) * Q n ≡ T n * Q (suc n) + delta n * Q n
sourceAdjacentCrossIdentity n
  rewrite prefixTStep n | prefixQStep n =
  solve 4
    (λ t q d v →
      ((t :* q :+ d) :* v) := (t :* (v :* q) :+ d :* v))
    refl (T n) (CH.sourceQ n) (delta n) (Q n)

-- The signed edge at n+1 is the same original product transported
-- through the next indexed leaf, not an unrelated residual.
sourceDeltaStep : (n : Nat) →
  delta (suc n) ≡ (P n * CH.sourceP n) * CH.sourceP (suc n) * a (suc n)
sourceDeltaStep n rewrite prefixPStep n = refl

-- Local adjacent-window geometry: a step d followed by -e in the
-- common scaled chart preserves the shared endpoint and leaves d-e.
-- Signs and magnitude domination must be proved by the actual source.
adjacentTurnConservation : (t d e q : ℤ) →
  ((t + d) * q + e) ≡ t * q + (d * q + e)
adjacentTurnConservation t d e q =
  solve 4
    (λ t d e q → (((t :+ d) :* q) :+ e)
      := ((t :* q) :+ (d :* q :+ e)))
    refl t d e q
