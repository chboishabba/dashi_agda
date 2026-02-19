module DASHI.Algebra.UnitaryVsCollapse where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary      using (¬_)
open import Data.Nat              using (_<_)
open import Data.Empty            using (⊥; ⊥-elim)

-- A minimal invertible step system with a Nat-valued measure.
record InvertibleNat (S : Set) : Set₁ where
  field
    step  : S → S
    inv   : S → S
    left  : ∀ s → inv (step s) ≡ s
    right : ∀ s → step (inv s) ≡ s
    H     : S → Nat

open InvertibleNat public

-- Iteration
iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate f zero    s = s
iterate f (suc n) s = iterate f n (f s)

-- If you have strict decrease everywhere, you get an infinite descent
-- along iterates, which is impossible in Nat.
--
-- To keep this module lightweight, we package the “no infinite descent”
-- fact as a single lemma that can be discharged from stdlib later.
--
-- (If you want, I can give the fully discharged stdlib proof too.)
postulate
  NatNoInfiniteDescent :
    ∀ {S : Set} (H : S → Nat) (f : S → S) (s₀ : S) →
    (∀ s → H (f s) < H s) → ⊥

-- Main theorem: in an inhabited system, “strict collapse everywhere” is impossible.
no-global-strict-collapse :
  ∀ {S : Set} (U : InvertibleNat S) →
  (s₀ : S) →
  ¬ (∀ s → H U (step U s) < H U s)
no-global-strict-collapse U s₀ strict =
  NatNoInfiniteDescent (H U) (step U) s₀ strict
