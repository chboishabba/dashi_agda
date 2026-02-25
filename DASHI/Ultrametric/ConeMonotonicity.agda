{-# OPTIONS --safe #-}

module DASHI.Ultrametric.ConeMonotonicity where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (¬_)

record Ultrametric {ℓx ℓd} (X : Set ℓx) (D : Set ℓd) : Set (lsuc (ℓx ⊔ ℓd)) where
  field
    d : X → X → D

record StrictProgress {ℓx ℓd} {X : Set ℓx} {D : Set ℓd}
  (U : Ultrametric X D) : Set (lsuc (ℓx ⊔ ℓd)) where
  field
    _<_ : D → D → Set _
    nonTie : ∀ {x} → ¬ (_<_ x x)

record ConeMono {ℓx ℓd} {X : Set ℓx} {D : Set ℓd}
  (U : Ultrametric X D) (T : X → X)
  : Set (lsuc (ℓx ⊔ ℓd)) where
  field
    _≤_ : D → D → Set _
    NonZero : D → Set _
    mono : ∀ {x y} → NonZero (d U x y) → _≤_ (d U (T x) (T y)) (d U x y)
