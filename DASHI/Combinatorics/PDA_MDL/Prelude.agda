module DASHI.Combinatorics.PDA_MDL.Prelude where

open import Data.Nat public
  renaming (ℕ to Nat)
open import Data.List public using (List; []; _∷_)
open import Data.Product public using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤; tt)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; cong; sym; trans)
open import Data.Nat.Properties public using (≤-refl; ≤-trans)

¬_ : Set → Set
¬ A = A → ⊥

fst : ∀ {A : Set} {B : A → Set} → Σ A B → A
fst = proj₁

snd : ∀ {A : Set} {B : A → Set} (p : Σ A B) → B (proj₁ p)
snd = proj₂

CodeLength : Set
CodeLength = Nat
