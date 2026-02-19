module DASHI.Combinatorics.Entropy where

open import DASHI.Core.Prelude

record Entropy (S : Set) : Set₁ where
  field H : S → Nat

zero≤ : ∀ n → zero ≤ n
zero≤ _ = z≤n

entropy-nonneg : ∀ {S} (E : Entropy S) (x : S) → 0 ≤ Entropy.H E x
entropy-nonneg E x = zero≤ (Entropy.H E x)

record Involution (S : Set) : Set₁ where
  field ι : S → S
        invol : ∀ x → ι (ι x) ≡ x

record EntropyInvariant {S : Set} (E : Entropy S) (I : Involution S) : Set where
  field invH : ∀ x → Entropy.H E (Involution.ι I x) ≡ Entropy.H E x
