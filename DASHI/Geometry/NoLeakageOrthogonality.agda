{-# OPTIONS --allow-unsolved-metas #-}
module DASHI.Geometry.NoLeakageOrthogonality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

-- Abstract vector space / inner-product interfaces
postulate
  V : Set
  _+_ _-_ _*_ : V → V → V
  0v : V

  ⟪_,_⟫ : V → V → V
  ∥_∥² : V → V
  two : V

postulate
  add-norm² :
    ∀ a b → ∥ a + b ∥² ≡ (∥ a ∥² + ∥ b ∥²) + (two * ⟪ a , b ⟫)

record Projection : Set₁ where
  field
    P : V → V
    idem : ∀ x → P (P x) ≡ P x
    split : ∀ x → P x + (x - P x) ≡ x

coarse : Projection → V → V
coarse Pr x = Projection.P Pr x

detail : Projection → V → V
detail Pr x = x - Projection.P Pr x

NoLeakage : Projection → Set
NoLeakage Pr =
  ∀ x → ∥ x ∥² ≡ ∥ coarse Pr x ∥² + ∥ detail Pr x ∥²

Orthogonal : Projection → Set
Orthogonal Pr =
  ∀ x → ⟪ coarse Pr x , detail Pr x ⟫ ≡ 0v

postulate
  cancel-add-left : ∀ {a c} → a ≡ a + c → c ≡ 0v
  div2-zero : ∀ {z} → two * z ≡ 0v → z ≡ 0v

NoLeakage⇒Orthogonal :
  ∀ (Pr : Projection) →
  NoLeakage Pr →
  Orthogonal Pr
NoLeakage⇒Orthogonal Pr NL x =
  let open Projection Pr
      c = coarse Pr x
      d = detail Pr x
      eq1 = NL x
      eq2 = add-norm² c d
      eqSplit = sym (cong (λ z → ∥ z ∥²) (split x))
      eq2' = trans eqSplit eq2
      eq3 = trans (sym eq1) eq2'
  in
  div2-zero (cancel-add-left eq3)
