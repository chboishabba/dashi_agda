module DASHI.Prelude where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)

data ⊥ : Set where
record ⊤ : Set where constructor tt

¬_ : Set → Set
¬ A = A → ⊥

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

infixr 3 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 2 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
