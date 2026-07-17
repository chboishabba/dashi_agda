module DASHI.Physics.YangMills.BalabanIntervalConstraintComposition where

-- Semigroup law for Bałaban's composed averaging constraints.
--
-- The dependent scale spaces mean the endpoints `(m + n) + k` and
-- `m + (n + k)` are propositionally, rather than definitionally, equal.  This
-- module makes that transport explicit and proves that a length-`m+n`
-- constraint equals a length-`n` constraint followed by a length-`m`
-- constraint.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalConstraintChain using
  ( intervalConstraint )

-- This proof is kept in the same module as `transport`, so all dependent uses
-- reduce against one canonical equality witness rather than extensionally
-- equal but definitionally distinct `cong` implementations.
natAddAssocTransport :
  ∀ a b c →
  (a + b) + c ≡ a + (b + c)
natAddAssocTransport zero b c = refl
natAddAssocTransport (suc a) b c =
  cong suc (natAddAssocTransport a b c)

transport :
  (Space : ℕ → Set) →
  ∀ {i j} →
  i ≡ j →
  Space i → Space j
transport Space refl x = x

-- Transport through the successor equality commutes with the adjacent map.
transportStep :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  ∀ {i j} →
  (indexEquality : i ≡ j) →
  (x : Space i) →
  transport Space (cong suc indexEquality) (Q i x)
    ≡ Q j (transport Space indexEquality x)
transportStep Space Q refl x = refl

intervalConstraintAppend :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  ∀ k n m →
  (x : Space k) →
  transport Space (natAddAssocTransport m n k)
    (intervalConstraint Space Q k (m + n) x)
  ≡ intervalConstraint Space Q (n + k) m
      (intervalConstraint Space Q k n x)
intervalConstraintAppend Space Q k n zero x = refl
intervalConstraintAppend Space Q k n (suc m) x =
  let
    indexEquality = natAddAssocTransport m n k
    prefix = intervalConstraint Space Q k (m + n) x
    p1 = transportStep Space Q indexEquality prefix
    p2 = cong
      (Q (m + (n + k)))
      (intervalConstraintAppend Space Q k n m x)
  in
    trans p1 p2
