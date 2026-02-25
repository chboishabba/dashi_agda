module DASHI.Geometry.MaskedQuadratic where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Vec using (Vec; zipWith; []; _∷_)
open import Data.Product using (Σ; _,_)

open import DASHI.Core.Q using (ℚ; _*ℚ_; _+ℚ_; 0ℚ)

sumℚ : ∀ {n} → Vec ℚ n → ℚ
sumℚ {zero} [] = 0ℚ
sumℚ {suc n} (x ∷ xs) = x +ℚ sumℚ xs

data Signature : Set where
  sig31 sig13 sig22 sig40 sig04 : Signature

record MaskedQuadratic (n : Nat) : Set₁ where
  field
    V      : Set
    vec    : V → Vec ℚ n
    mask   : Vec ℚ n
    Q      : V → ℚ
    Q-def  : ∀ x →
      Q x ≡ sumℚ (zipWith (λ m xi → (m *ℚ xi) *ℚ xi) mask (vec x))
    signature : Σ Nat (λ p → Σ Nat (λ q → p + q ≡ n))
    signatureTag : Signature
    nondeg : Set

open MaskedQuadratic public
