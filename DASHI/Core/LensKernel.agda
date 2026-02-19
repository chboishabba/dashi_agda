module DASHI.Core.LensKernel where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

record Lens (S : Set) (A : Set) : Set₁ where
  field
    observe : S → A

-- Exact commutation: observe (K x) = observe x
record LensInvariant {S A : Set} (L : Lens S A) (K : S → S) : Set where
  field inv : ∀ x → Lens.observe L (K x) ≡ Lens.observe L x

-- Monotone variant (when observations are ordered)
record Preorder (A : Set) : Set₁ where
  field _⊑_ : A → A → Set
        refl⊑ : ∀ a → a ⊑ a
        trans⊑ : ∀ a b c → a ⊑ b → b ⊑ c → a ⊑ c

record LensMonotone {S A : Set} (P : Preorder A) (L : Lens S A) (K : S → S) : Set where
  open Preorder P
  field mono : ∀ x → Lens.observe L (K x) ⊑ Lens.observe L x
