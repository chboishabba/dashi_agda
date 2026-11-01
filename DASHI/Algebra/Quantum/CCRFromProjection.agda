module DASHI.Algebra.Quantum.CCRFromProjection where

open import Agda.Builtin.Equality using (_≡_)

-- Parameterised CCR/Weyl data so this module is non-vacuous.
record CCRData : Set₁ where
  field
    ℚ : Set
    _*q_ : ℚ → ℚ → ℚ
    Hilbert : Set
    U : Set
    _∙_ : U → U → U
    Iu : U
    XTrans : ℚ → U
    PTrans : ℚ → U
    phase : ℚ → U
    P : Hilbert → Hilbert
    idem : ∀ x → P (P x) ≡ P x
    actX : ℚ → Hilbert → Hilbert
    actP : ℚ → Hilbert → Hilbert

Weyl : (D : CCRData) → Set
Weyl D =
  ∀ a b →
    CCRData._∙_ D (CCRData.XTrans D a) (CCRData.PTrans D b) ≡
    CCRData._∙_ D (CCRData.phase D (CCRData._*q_ D a b))
                   (CCRData._∙_ D (CCRData.PTrans D b) (CCRData.XTrans D a))

record ProjectionWeylAxioms (D : CCRData) : Set₁ where
  open CCRData D
  field
    weyl : Weyl D
    proj-inv-P : ∀ b ψ → P (actP b ψ) ≡ P ψ
    proj-covar-X : ∀ a ψ → P (actX a ψ) ≡ actX a (P ψ)

CCR : CCRData → Set₁
CCR D = ProjectionWeylAxioms D

stone-vn : ∀ {D} → ProjectionWeylAxioms D → CCR D
stone-vn axioms = axioms
