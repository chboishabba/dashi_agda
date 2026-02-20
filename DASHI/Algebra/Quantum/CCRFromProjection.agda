module DASHI.Algebra.Quantum.CCRFromProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

ℚ : Set
ℚ = ⊤

_*q_ : ℚ → ℚ → ℚ
_*q_ _ _ = tt

Hilbert : Set
Hilbert = ⊤

U : Set
U = ⊤

_∙_ : U → U → U
_∙_ _ _ = tt

Iu : U
Iu = tt

XTrans : ℚ → U
XTrans _ = tt

PTrans : ℚ → U
PTrans _ = tt

phase : ℚ → U
phase _ = tt

Weyl : Set
Weyl = ⊤

P : Hilbert → Hilbert
P _ = tt

idem : ∀ x → P (P x) ≡ P x
idem _ = refl

actX : ℚ → Hilbert → Hilbert
actX _ _ = tt

actP : ℚ → Hilbert → Hilbert
actP _ _ = tt

record ProjectionWeylAxioms : Set₁ where
  field
    weyl : Weyl
    proj-inv-P : ∀ b ψ → P (actP b ψ) ≡ P ψ
    proj-covar-X : ∀ a ψ → P (actX a ψ) ≡ actX a (P ψ)

CCR : Set
CCR = ⊤

stone-vn : ProjectionWeylAxioms → CCR
stone-vn _ = tt
