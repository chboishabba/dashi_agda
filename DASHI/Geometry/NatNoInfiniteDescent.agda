module DASHI.Geometry.NatNoInfiniteDescent where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat              using (_<_)
open import Data.Nat.Induction    using (Acc; acc; <-wellFounded)
open import Data.Empty            using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong)

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate f zero    s = s
iterate f (suc n) s = iterate f n (f s)

-- No infinite strict descent on Nat:
-- If H(f s) < H s for all s, then starting from s₀ you get an infinite
-- descending chain in Nat, which contradicts accessibility.
NatNoInfiniteDescent :
  ∀ {S : Set} (H : S → Nat) (f : S → S) (s₀ : S) →
  (∀ s → H (f s) < H s) → ⊥
NatNoInfiniteDescent {S} H f s₀ dec =
  bad s₀ (<-wellFounded (H s₀))
  where
    bad : ∀ s → Acc _<_ (H s) → ⊥
    bad s (acc wf) = bad (f s) (wf (dec s))
