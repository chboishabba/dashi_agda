module DASHI.Geometry.CliffordGate where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Minimal Clifford gate: structure-only (no analytic geometry).
-- This is the smallest honest bridge from a bilinear form to
-- a Clifford-algebra presentation.

record BilinearForm {ℓv ℓs : Level} (V : Set ℓv) (S : Set ℓs)
  : Set (lsuc (ℓv ⊔ ℓs)) where
  field
    ⟪_,_⟫ : V → V → S
open BilinearForm public

record RingLike {ℓ : Level} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    _+_ _*_ : S → S → S
    -_      : S → S
    0# 1#   : S
open RingLike public

-- Abstract Clifford algebra over (V,⟪,⟫).
record CliffordAlgebra
  {ℓv ℓs ℓa : Level}
  (V : Set ℓv) (S : Set ℓs)
  (R : RingLike S)
  (B : BilinearForm V S)
  : Set (lsuc (ℓv ⊔ ℓs ⊔ ℓa)) where
  field
    Carrier : Set ℓa
    _·_     : Carrier → Carrier → Carrier
    1A      : Carrier
    scalar  : S → Carrier
    embed   : V → Carrier

    -- Clifford relation: v·v = ⟪v,v⟫·1
    clifford :
      ∀ v → _·_ (embed v) (embed v) ≡
            scalar (BilinearForm.⟪_,_⟫ B v v)
open CliffordAlgebra public

-- Minimal Dirac-operator interface (no differential geometry yet).
record DiracOperator
  {ℓv ℓs ℓa ℓψ : Level}
  (V : Set ℓv) (S : Set ℓs) (Ψ : Set ℓψ)
  (R : RingLike S)
  (B : BilinearForm V S)
  (Cl : CliffordAlgebra {ℓa = ℓa} V S R B)
  : Set (lsuc (ℓv ⊔ ℓs ⊔ ℓa ⊔ ℓψ)) where
  field
    D : Ψ → Ψ
open DiracOperator public
