module DASHI.Geometry.SpinGate where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.CliffordGate

------------------------------------------------------------------------
-- Minimal Spin interface (structure-only).

record SpinGroup
  {ℓv ℓs ℓa ℓg : Level}
  (V : Set ℓv) (S : Set ℓs)
  (R : RingLike S)
  (B : BilinearForm V S)
  (Cl : CliffordAlgebra {ℓa = ℓa} V S R B)
  : Set (lsuc (ℓv ⊔ ℓs ⊔ ℓa ⊔ ℓg)) where
  field
    G    : Set ℓg
    act  : G → V → V
    presB : ∀ g x y → BilinearForm.⟪_,_⟫ B (act g x) (act g y) ≡ BilinearForm.⟪_,_⟫ B x y
open SpinGroup public

------------------------------------------------------------------------
-- Minimal Dirac-operator construction stub tied to the forced metric.

record DiracFromMetric
  {ℓv ℓs ℓa ℓψ : Level}
  (V : Set ℓv) (S : Set ℓs) (Ψ : Set ℓψ)
  (R : RingLike S)
  (B : BilinearForm V S)
  (Cl : CliffordAlgebra {ℓa = ℓa} V S R B)
  : Set (lsuc (ℓv ⊔ ℓs ⊔ ℓa ⊔ ℓψ)) where
  field
    D : Ψ → Ψ
open DiracFromMetric public
