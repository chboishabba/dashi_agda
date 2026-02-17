module DASHI.String.Unitary where

open import Agda.Builtin.Equality
open import DASHI.String.HilbertToy

record Unitary (H : InnerProductSpace) : Set where
  open InnerProductSpace H

  field
    U  : V → V
    U⁻¹ : V → V

    leftInv  : ∀ x → U⁻¹ (U x) ≡ x
    rightInv : ∀ x → U (U⁻¹ x) ≡ x

    preservesIP :
      ∀ x y → ⟨ U x , U y ⟩ ≡ ⟨ x , y ⟩
