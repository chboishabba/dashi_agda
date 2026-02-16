module DASHI.Entropy where

open import DASHI.Prelude
open import Data.Nat using (Nat)
open import Data.Nat.Properties using (z≤n)
open import Data.Nat using (_≤_)

record Entropy (S : Set) : Set₁ where
  field H : S → Nat

entropy-nonneg : ∀ {S} (E : Entropy S) (x : S) → 0 ≤ Entropy.H E x
entropy-nonneg E x = z≤n

record Involution (S : Set) : Set₁ where
  field ι : S → S
        invol : ∀ x → ι (ι x) ≡ x

record EntropyInvariant {S : Set} (E : Entropy S) (I : Involution S) : Set where
  field invH : ∀ x → Entropy.H E (Involution.ι I x) ≡ Entropy.H E x
