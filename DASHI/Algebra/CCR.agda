module DASHI.Algebra.CCR where

open import Agda.Primitive
open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

-- An abstract carrier for operators. This needs to be parameterized by a level.
-- We use Level0 for now, but this could be (ℓ : Level) : Set (lsuc ℓ) as suggested.
record Op (S : Set) (ℓ : Level) : Set (lsuc ℓ) where
  field
    apply : S → S

-- A basic definition of composition (operator product)
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

_Op∘_ : ∀ {S ℓ} → Op S ℓ → Op S ℓ → Op S ℓ
_Op∘_ {S} {ℓ} op1 op2 = record { apply = (Op.apply op1) ∘ (Op.apply op2) }

-- Commutator for two operators (requires an abstract subtraction on S)
_commutator_ : ∀ {S ℓ} → (S → S → S) → Op S ℓ → Op S ℓ → Op S ℓ
_commutator_ {S} {ℓ} sub op1 op2 =
  record { apply = λ x → sub (Op.apply op1 (Op.apply op2 x))
                          (Op.apply op2 (Op.apply op1 x)) }

-- A single axiom bundle for the CCR story.
record CCRFramework {S ℓ} : Set (lsuc ℓ) where
  field
    sub : S → S → S
    Hilbert : Set
    OpNorm : Op S ℓ → Set
    OpConvergence : (Nat → Op S ℓ) → Op S ℓ → Set
    CCR : Set

open CCRFramework public
