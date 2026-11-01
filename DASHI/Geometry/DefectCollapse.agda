module DASHI.Geometry.DefectCollapse where

open import Level using (Level; suc; _⊔_)

record DefectCollapse {ℓx ℓe}
  (X : Set ℓx) (E : Set ℓe)
  : Set (suc (ℓx ⊔ ℓe)) where
  field
    D : X → X
    T : X → X
    _≤_ : E → E → Set ℓe
    energy : X → E
    collapse : ∀ x → _≤_ (energy (D (T x))) (energy (D x))

open DefectCollapse public
