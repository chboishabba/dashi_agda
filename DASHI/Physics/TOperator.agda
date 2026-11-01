module DASHI.Physics.TOperator where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Combinatorics.Entropy using (Involution)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_

-- Real operator scaffold: T = C ∘ P ∘ R
record TOperator (S : Set) : Set₁ where
  field
    C : S → S
    P : S → S
    R : S → S

  T : S → S
  T = C ∘ (P ∘ R)

-- Optional equivariance with involution.
record TEquivariant (S : Set) (op : TOperator S) (inv : Involution S) : Set₁ where
  field
    involutionCommutes : ∀ x →
      TOperator.T op (Involution.ι inv x) ≡ Involution.ι inv (TOperator.T op x)
