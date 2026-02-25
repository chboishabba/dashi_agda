module DASHI.Geometry.Parallelogram where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_; twoℚ)

record AdditiveSpace (ℓ : Level) : Set (suc ℓ) where
  field
    V   : Set ℓ
    _+_ : V → V → V
    _-_ : V → V → V

record NormedSpace (ℓ : Level) : Set (suc ℓ) where
  field
    V : Set ℓ
    _+_ : V → V → V
    _-_ : V → V → V
    ‖_‖ : V → ℚ

Parallelogram :
  ∀ {ℓ} (N : NormedSpace ℓ) → Set ℓ
Parallelogram {ℓ} N =
  let open NormedSpace N in
  ∀ x y →
    ((‖ x + y ‖ *ℚ ‖ x + y ‖) +ℚ (‖ x - y ‖ *ℚ ‖ x - y ‖))
      ≡
    ((twoℚ *ℚ (‖ x ‖ *ℚ ‖ x ‖)) +ℚ (twoℚ *ℚ (‖ y ‖ *ℚ ‖ y ‖)))
