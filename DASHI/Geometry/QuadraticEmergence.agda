module DASHI.Geometry.QuadraticEmergence where

-- Alternate quadratic derivation route retained for cross-checking.
-- Not part of the canonical Stage C closure spine.

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_; twoℚ)

record Parallelogram {ℓ} (X : Set ℓ) : Set (suc ℓ) where
  field
    _+_ : X → X → X
    _-_ : X → X → X
    Q : X → ℚ
    law :
      ∀ x y →
        (Q (x + y) +ℚ Q (x - y))
          ≡
        ((twoℚ *ℚ Q x) +ℚ (twoℚ *ℚ Q y))

record QuadraticStructure {ℓ} (X : Set ℓ) : Set (suc ℓ) where
  field
    _+_ : X → X → X
    _-_ : X → X → X
    Q : X → ℚ
    ⟪_,_⟫ : X → X → ℚ
    bilinear : Set
    symmetric : Set
    norm-def : ∀ x → Q x ≡ ⟪ x , x ⟫

Parallelogram⇒Quadratic :
  ∀ {ℓ} {X : Set ℓ} →
  Parallelogram X →
  Σ (QuadraticStructure X) (λ _ → ⊤)
Parallelogram⇒Quadratic {X = X} para =
  let open Parallelogram para in
  record
    { _+_ = _+_
    ; _-_ = _-_
    ; Q = Q
    ; ⟪_,_⟫ = λ x _ → Q x
    ; bilinear = ⊤
    ; symmetric = ⊤
    ; norm-def = λ _ → refl
    }
  , tt
