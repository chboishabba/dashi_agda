module DASHI.Geometry.NoLeakageOrthogonality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

----------------------------------------------------------------
-- Inner-product data supplied as assumptions (no metas/stubs).
----------------------------------------------------------------

record InnerProductData : Set₁ where
  field
    V : Set
    _+_ _-_ _*_ : V → V → V
    0v : V
    two : V
    ⟪_,_⟫ : V → V → V
    ∥_∥² : V → V
    add-norm² :
      ∀ a b → ∥ a + b ∥² ≡ (∥ a ∥² + ∥ b ∥²) + (two * ⟪ a , b ⟫)
    cancel-add-left : ∀ {a c} → a ≡ a + c → c ≡ 0v
    div2-zero : ∀ {z} → two * z ≡ 0v → z ≡ 0v

----------------------------------------------------------------
-- Projections and “no leakage ⇒ orthogonality”
----------------------------------------------------------------

record Projection (D : InnerProductData) : Set₁ where
  open InnerProductData D
  field
    P : V → V
    idem : ∀ x → P (P x) ≡ P x
    split : ∀ x → P x + (x - P x) ≡ x

coarse : ∀ {D} → Projection D → InnerProductData.V D → InnerProductData.V D
coarse Pr x = Projection.P Pr x

detail : ∀ {D} → Projection D → InnerProductData.V D → InnerProductData.V D
detail {D} Pr x =
  let open InnerProductData D in x - Projection.P Pr x

NoLeakage : ∀ {D} → Projection D → Set
NoLeakage {D} Pr =
  ∀ x → ∥ x ∥² ≡ ∥ coarse Pr x ∥² + ∥ detail Pr x ∥²
  where open InnerProductData D

Orthogonal : ∀ {D} → Projection D → Set
Orthogonal {D} Pr =
  ∀ x → ⟪ coarse Pr x , detail Pr x ⟫ ≡ 0v
  where open InnerProductData D

NoLeakage⇒Orthogonal :
  ∀ {D} (Pr : Projection D) →
  NoLeakage Pr →
  Orthogonal Pr
NoLeakage⇒Orthogonal {D} Pr NL x =
  let open Projection Pr
      open InnerProductData D
      c = coarse Pr x
      d = detail Pr x
      eq1 = NL x
      eq2 = add-norm² c d
      eqSplit = sym (cong (λ z → ∥ z ∥²) (split x))
      eq2' = trans eqSplit eq2
      eq3 = trans (sym eq1) eq2'
  in
  div2-zero (cancel-add-left eq3)
