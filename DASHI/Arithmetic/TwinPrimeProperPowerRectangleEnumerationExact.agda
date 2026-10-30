module DASHI.Arithmetic.TwinPrimeProperPowerRectangleEnumerationExact where

------------------------------------------------------------------------
-- CT11, FINITE RECTANGULAR CANDIDATE ENUMERATOR AND EXACT CARDINALITY
--
-- ORIGINAL OWNERS (import, do not duplicate): 
--  * DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact.listLength
--  * DASHI.Analysis.RiemannPrimePowerArithmetic.natPow
--  * CT10 bound: TwinPrimeProperPowerRectangleBoundExact
--
-- The coordinate rectangle contains all positive bases 1..B, and
-- exponent-index candidates k=0..E-1 (actual exponent k+2).
-- It deliberately OVERCOUNTS composite bases and repeated values.
-- This makes it suitable for a later upper bound, not a claim of
-- unique prime-power representation or completed M15.
--
-- Source-written, Agda kernel pending. No postulate, no ESD edit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)\nopen import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)\nopen import Data.Nat.Base using (_≤_; z≤n; s≤s)\nimport Data.Nat.Properties as NatP\nopen import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; subst)
open import Data.List.Base using (_++_; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power

-- All exponent indices 0..E-1 appear, in descending order.
powerRow : Nat → Nat → List (Nat × Nat)
powerRow base zero = []
powerRow base (suc e) = (base , e) ∷ powerRow base e

powerRowLength : (base e : Nat) →
  Reindex.listLength (powerRow base e) ≡ e
powerRowLength base zero = refl
powerRowLength base (suc e) =
  cong suc (powerRowLength base e)

-- All bases 1..B, each paired with all E exponent indices.
powerRectangle : Nat → Nat → List (Nat × Nat)
powerRectangle zero e = []
powerRectangle (suc b) e =
  powerRow (suc b) e ++ powerRectangle b e

appendLength :
  {A : Set} (xs ys : List A) →
  Reindex.listLength (xs ++ ys)
    ≡ Reindex.listLength xs + Reindex.listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys = cong suc (appendLength xs ys)

powerRectangleLength : (b e : Nat) →
  Reindex.listLength (powerRectangle b e) ≡ b * e
powerRectangleLength zero e = refl
powerRectangleLength (suc b) e =
  trans
    (appendLength (powerRow (suc b) e) (powerRectangle b e))
    (cong₂ _+_
      (powerRowLength (suc b) e)
      (powerRectangleLength b e))

powerValue : Nat × Nat → Nat
powerValue (base , exponentIndex) =
  Power.natPow base (suc (suc exponentIndex))

-- Enumerates the candidate powers without either deduplicating
-- or asserting they are prime powers (bases may be composite).
powerValueRectangle : Nat → Nat → List Nat
powerValueRectangle b e = map powerValue (powerRectangle b e)

mapLength :
  {A B : Set} (f : A → B) (xs : List A) →
  Reindex.listLength (map f xs) ≡ Reindex.listLength xs
mapLength f [] = refl
mapLength f (x ∷ xs) = cong suc (mapLength f xs)

powerValueRectangleLength : (b e : Nat) →
  Reindex.listLength (powerValueRectangle b e) ≡ b * e
powerValueRectangleLength b e =
  trans
    (mapLength powerValue (powerRectangle b e))
    (powerRectangleLength b e)

-- Independently filtered candidate lists cannot exceed the full
-- rectangle count. This is a pure finite fact, not analytic density.
filterCandidate : {A : Set} → (A → Bool) → List A → List A
filterCandidate predicate [] = []
filterCandidate predicate (x ∷ xs) with predicate x
... | true = x ∷ filterCandidate predicate xs
... | false = filterCandidate predicate xs

filteredLengthAtMost :
  {A : Set} (predicate : A → Bool) (xs : List A) →
  Reindex.listLength (filterCandidate predicate xs)
    ≤ Reindex.listLength xs
filteredLengthAtMost predicate [] = z≤n
filteredLengthAtMost predicate (x ∷ xs)
  with predicate x
... | true = s≤s (filteredLengthAtMost predicate xs)
... | false =
  NatP.≤-step (filteredLengthAtMost predicate xs)

filteredRectangleAtMost :
  (b e : Nat) (predicate : (Nat × Nat) → Bool) →
  Reindex.listLength (filterCandidate predicate (powerRectangle b e))
    ≤ b * e
filteredRectangleAtMost b e predicate =
  subst
    (λ n → Reindex.listLength
      (filterCandidate predicate (powerRectangle b e)) ≤ n)
    (powerRectangleLength b e)
    (filteredLengthAtMost predicate (powerRectangle b e))
