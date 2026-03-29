module DASHI.Physics.PhysicalTheory where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)

record PhysicalTheory (ℓ : Level) : Set (lsuc ℓ) where
  field
    State      : Set ℓ
    step       : State → State

    Defect     : State → Set ℓ
    defectSize : State → Nat

    Inv        : State → Set ℓ
    inv-step   : ∀ {x} → Inv x → Inv (step x)

    defect-monotone :
      ∀ {x} → Inv x → defectSize (step x) ≤ defectSize x

    fixed        : State → Set ℓ
    recoveredLaw : State → Set ℓ

open PhysicalTheory public
