module DASHI.Geometry.Polarization where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; fourℚ)

record Polarization (ℓ : Level) : Set (suc ℓ) where
  field
    V : Set ℓ
    _+_ : V → V → V
    _-_ : V → V → V
    Q : V → ℚ
    ⟪_,_⟫ : V → V → ℚ
    polarization :
      ∀ x y → fourℚ *ℚ ⟪ x , y ⟫ ≡ Q (x + y) -ℚ Q (x - y)

open Polarization public
