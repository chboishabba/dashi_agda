module Verification.Prelude where

open import Data.Nat public
  renaming (ℕ to Nat)
open import Data.Bool public using (Bool; true; false)
open import Data.List public using (List; []; _∷_)
open import Data.Product public using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤; tt)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; cong; sym; trans)

¬_ : Set → Set
¬ A = A → ⊥

fst : ∀ {A : Set} {B : A → Set} → Σ A B → A
fst = proj₁

snd : ∀ {A : Set} {B : A → Set} (p : Σ A B) → B (proj₁ p)
snd = proj₂
