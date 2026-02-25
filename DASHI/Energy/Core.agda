{-# OPTIONS --safe #-}

module DASHI.Energy.Core where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)

record Preorder {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _≤_ : A → A → Set ℓ
    refl : ∀ x → x ≤ x
    trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

record EnergySpace {ℓx ℓe} (X : Set ℓx) (E : Set ℓe) : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    P : Preorder E
    energy : X → E

open Preorder public
open EnergySpace public

record Endo {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field T : X → X
