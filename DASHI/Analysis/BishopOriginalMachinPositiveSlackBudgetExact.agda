module DASHI.Analysis.BishopOriginalMachinPositiveSlackBudgetExact where

-- ORIGINAL HALF-RADIUS MACHIN BUDGET: NONNEGATIVE INTEGER RESIDUAL.
-- Source-written; Agda native typecheck pending.
--
-- Instead of subtracting rational correction tails in an abstract
-- ordered field, use the exact positive Nat slack recurrence:
--
--   p_0=1;       p_(n+1)=4*p_n          (=4^n),
--   s_0=0;       s_(n+1)=4*s_n+9*n,
--   linear(n)=3*n+1,
--   p_n=linear(n)+s_n.
--
-- Hence the positive fraction
--   B_n = 8*s_n/(9*p_n)
-- has the correct Machin budget recurrence:
--   B_(n+1)=B_n + 2*n/p_n,
-- with B_n <= 8/9 from s_n<=p_n.
--
-- All finite arithmetic uses the source Nat/unnormalised rational
-- carrier. The remaining qRadiusBudget=B equality is a concrete
-- rational recurrence weld, not an arbitrary analyticity premise.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import Data.Nat.Properties as NP
open import Data.Nat.Base using (_≤_; NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst; subst₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _≤_)
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as FractionOrder

powerFour : Nat → Nat
powerFour zero = 1
powerFour (suc n) = 4 * powerFour n

linear : Nat → Nat
linear n = 3 * n + 1

slack : Nat → Nat
slack zero = 0
slack (suc n) = 4 * slack n + 9 * n

powerFourPositive : (n : Nat) → 1 ≤ powerFour n
powerFourPositive zero = NP.≤-refl
powerFourPositive (suc n) =
  subst (λ z → 1 ≤ z)
    (sym (solve 1 (λ p → con 4 :* p := p :+ (con 3 :* p))
      refl (powerFour n)))
    (NP.≤-trans
      (powerFourPositive n)
      (NP.m≤m+n (powerFour n) (3 * powerFour n)))

-- The exact 4^n decomposition is a nonnegative integer identity.
powerFourDecomposition : (n : Nat) →
  powerFour n ≡ linear n + slack n
powerFourDecomposition zero = refl
powerFourDecomposition (suc n) =
  trans
    (cong (λ p → 4 * p) (powerFourDecomposition n))
    (solve 2
      (λ k s →
        con 4 :* ((con 3 :* k :+ con 1) :+ s)
        := ((con 3 :* (k :+ con 1)) :+ con 1)
           :+ ((con 4 :* s) :+ (con 9 :* k)))
      refl n (slack n))

slackBelowPowerFour : (n : Nat) → slack n ≤ powerFour n
slackBelowPowerFour n =
  subst (λ z → slack n ≤ z)
    (sym (powerFourDecomposition n))
    (NP.m≤n+m (slack n) (linear n))

-- Use the SAME original unnormalised Nat NonZero constructor used by
-- BishopMachinCrossEnvelopeBishopOrderExact. No denominator supplied as
-- a free theorem argument to the subsequent rational order.
powerFourNonZero : (n : Nat) → NonZero (powerFour n)
powerFourNonZero zero = _
powerFourNonZero (suc n) =
  NP.m*n≢0 4 (powerFour n)
    {{_}} {{powerFourNonZero n}}

positiveDenominatorNonZero :
  (n : Nat) → NonZero (9 * powerFour n)
positiveDenominatorNonZero n =
  NP.m*n≢0 9 (powerFour n)
    {{_}} {{powerFourNonZero n}}

-- Positive rational residual B_n = 8*s_n/(9*p_n).
positiveBudget : Nat → ℚᵘ
positiveBudget n =
  let instance
        denominatorNZ = positiveDenominatorNonZero n
  in (+ (8 * slack n) / (9 * powerFour n))

-- The integer cleared-denominator inequality uses only positivity
-- of the existing slack and the commutative Nat semiring solver.
positiveCrossOrder : (n : Nat) →
  (8 * slack n) * 9 ≤ 8 * (9 * powerFour n)
positiveCrossOrder n =
  let
    raw :
      (slack n * 8) * 9 ≤ (powerFour n * 8) * 9
    raw =
      NP.*-mono-≤
        (NP.*-mono-≤ (slackBelowPowerFour n) NP.≤-refl)
        NP.≤-refl
    leftReorder :
      ((slack n * 8) * 9) ≡ ((8 * slack n) * 9)
    leftReorder = solve 1
      (λ s → (s :* con 8) :* con 9
        := (con 8 :* s) :* con 9)
      refl (slack n)
    rightReorder :
      ((powerFour n * 8) * 9) ≡ (8 * (9 * powerFour n))
    rightReorder = solve 1
      (λ p → (p :* con 8) :* con 9
        := con 8 :* (con 9 :* p))
      refl (powerFour n)
  in subst₂ _≤_ leftReorder rightReorder raw

-- Fully inhabited constructive order bound, conditional on TYPECHECK
-- only; there is no new original-budget bound axiom here.
positiveBudgetBelowEightNinths :
  (n : Nat) → Q._≤_ (positiveBudget n) (+ 8 / 9)
positiveBudgetBelowEightNinths n =
  let instance
        denominatorNZ = positiveDenominatorNonZero n
  in FractionOrder.natFractionLe (positiveCrossOrder n)

-- Rational recurrence: positiveBudget(n+1) = positiveBudget(n)
--    + 2*n / 4^n.
-- Reuse the original Nat identity powerFourDecomposition, the
-- positive denominator proof above, and source Q.*≡* cross products.
-- This last equality to Readback.qRadiusBudget remains to be
-- implemented and checked natively before OriginalRationalBudgetOrder
-- can be inhabited.
