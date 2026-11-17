module DASHI.Foundations.BishopPellLucasIntegerInvariantExact where

------------------------------------------------------------------------
-- PELL-LUCAS DOUBLING: INTEGER INVARIANT, NO SECOND SQRT CARRIER
--
-- Classical Pell equation and Lucas-unit doubling.
-- This module deliberately does NOT define sqrt(2), sqrt(3), sqrt(6)
-- as new Bishop reals. The existing canonical producers are:
-- BishopNatSquareRootRegularFloorExact and
-- BishopNatSquareRootSemanticSquareExact.
--
-- Downstream rational width/positivity and Bishop setoid uniqueness
-- remain separately listed obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Data.Integer using (ℤ; 1ℤ; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

two : ℤ
two = 1ℤ + 1ℤ

square : ℤ → ℤ
square x = x * x

pNext qNext : ℤ → ℤ → ℤ → ℤ
pNext D p q = square p + D * square q
qNext D p q = two * p * q

doublingPellPolynomial :
  (D p q : ℤ) →
  square (pNext D p q) - D * square (qNext D p q)
  ≡ square (square p - D * square q)
doublingPellPolynomial D p q =
  solve 3
    (λ D p q →
      (((p :* p :+ D :* (q :* q))
          :* (p :* p :+ D :* (q :* q)))
        :- D :* (((Κ two :* p) :* q)
          :* ((Κ two :* p) :* q)))
      :=
      ((p :* p :- D :* (q :* q))
        :* (p :* p :- D :* (q :* q))))
    refl D p q

record PellUnit (D : ℤ) : Set where
  constructor pell-unit
  field
    p q : ℤ
    normOne : square p - D * square q ≡ 1ℤ
open PellUnit public

doubleUnit : ∀ {D} → PellUnit D → PellUnit D
doubleUnit {D} (pell-unit p q invariant) =
  pell-unit
    (pNext D p q)
    (qNext D p q)
    (trans
      (doublingPellPolynomial D p q)
      (trans (cong square invariant) refl))

iteratePell : ∀ {D} → Nat → PellUnit D → PellUnit D
iteratePell zero initial = initial
iteratePell (suc n) initial = doubleUnit (iteratePell n initial)

-- Original minimal solutions for D=2,3,6 are exact integer witnesses.
twoUnit : PellUnit two
twoUnit = pell-unit 3 2 refl

threeUnit : PellUnit 3
threeUnit = pell-unit 2 1 refl

sixUnit : PellUnit 6
sixUnit = pell-unit 5 2 refl

twoPell : Nat → PellUnit two
twoPell n = iteratePell n twoUnit

threePell : Nat → PellUnit 3
threePell n = iteratePell n threeUnit

sixPell : Nat → PellUnit 6
sixPell n = iteratePell n sixUnit

------------------------------------------------------------------------
-- No paid real-enclosure theorem is asserted in this module.
-- For positive p,q with p²-Dq²=1 the standard rationals
--   Dq/p < sqrt(D) < p/q
-- have exact width 1/(pq).
-- To promote to the existing Bishop sqrt, prove rational order,
-- a dyadic width schedule, positivity and unique nonnegative square
-- root using the original BishopNatSquareRootSemanticSquareExact.
------------------------------------------------------------------------
