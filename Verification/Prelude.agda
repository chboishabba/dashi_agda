module Verification.Prelude where

open import Agda.Builtin.Nat      using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

data ⊥ : Set where
record ⊤ : Set where constructor tt

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

infixr 3 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

¬_ : Set → Set
¬ A = A → ⊥
