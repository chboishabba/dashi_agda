{-# OPTIONS --safe #-}

module DASHI.Energy.TranslationInvariantMetric where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Energy.Core

record AddGroup {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    _+_ : X → X → X
    _-_ : X → X → X
    0#  : X

record TI
  {ℓx ℓe}
  (X : Set ℓx) (E : Set ℓe)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    G : AddGroup X
    d : X → X → E
    transInv : ∀ x y z →
      d (AddGroup._+_ G x z) (AddGroup._+_ G y z) ≡ d x y
