module DASHI.Geometry.NoStrictDescentForInvertible where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_<_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Empty using (⊥)

open import DASHI.Geometry.NatNoInfiniteDescent using (NatNoInfiniteDescent)

record InvertibleNat (S : Set) : Set where
  field
    step  : S → S
    inv   : S → S
    left  : ∀ s → inv (step s) ≡ s
    right : ∀ s → step (inv s) ≡ s
    H     : S → Nat

-- Invertible step implies you can “walk backwards forever”,
-- contradicting strict descent everywhere.
invertible-no-strict-descent :
  ∀ {S} (U : InvertibleNat S) →
  (s₀ : S) →
  ¬ (∀ s → InvertibleNat.H U (InvertibleNat.step U s) < InvertibleNat.H U s)
invertible-no-strict-descent U s₀ strict =
  NatNoInfiniteDescent (InvertibleNat.H U) (InvertibleNat.step U) s₀ strict
