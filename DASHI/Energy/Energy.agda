module DASHI.Energy.Energy where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Minimal preorder on a scalar type.
record Preorder {ℓ} : Set (suc ℓ) where
  field
    S    : Set ℓ
    _≤_  : S → S → Set ℓ
    refl≤ : ∀ x → x ≤ x
    trans≤ : ∀ x y z → x ≤ y → y ≤ z → x ≤ z

open Preorder public

-- Abstract energy / cost on a space, valued in a preorder.
record EnergySpace {ℓx ℓs} (X : Set ℓx) (P : Preorder {ℓs})
  : Set (suc (ℓx ⊔ ℓs)) where
  open Preorder P
  field
    E : X → X → Preorder.S P
    E-refl : ∀ x → Preorder._≤_ P (E x x) (E x x)
    -- Optional separation axiom; keep as a placeholder.
    E-sep : ∀ x y → Preorder._≤_ P (E x y) (E x x) → x ≡ y

open EnergySpace public
