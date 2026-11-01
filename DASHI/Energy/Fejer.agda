{-# OPTIONS --safe #-}

module DASHI.Energy.Fejer where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import DASHI.Energy.Core

record FejerPoint
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (ES : EnergySpace X E)
  (T : X → X)
  (x⋆ : X)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    d : X → X → E
    fejer : ∀ x →
      Preorder._≤_ (EnergySpace.P ES)
        (d (T x) x⋆)
        (d x x⋆)

record FejerSet
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (ES : EnergySpace X E)
  (T : X → X)
  (S : X → Set ℓx)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    d : X → X → E
    fejer : ∀ x y → S y →
      Preorder._≤_ (EnergySpace.P ES)
        (d (T x) y)
        (d x y)
