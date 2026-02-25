module DASHI.Geometry.OrthogonalityFromQuadratic where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Energy.Energy
open import DASHI.Energy.ClosestPoint

-- Abstract quadratic + polarization interface.
record QuadraticWithInner {ℓx ℓs} (X : Set ℓx) (P : Preorder {ℓs})
  : Set (suc (ℓx ⊔ ℓs)) where
  open Preorder P
  field
    Q : X → Preorder.S P
    ⟪_,_⟫ : X → X → Preorder.S P
    Q-def : ∀ x → Q x ≡ ⟪ x , x ⟫

open QuadraticWithInner public

-- Abstract linear/convex closure of FixP.
record FixSubspace {ℓx} {X : Set ℓx} (Pj : Projection X) : Set (suc ℓx) where
  field
    closed : ∀ x y → FixP Pj x → FixP Pj y → FixP Pj x  -- placeholder

open FixSubspace public

-- Corollary target: orthogonality of projection and defect.
record OrthogonalityCorollary {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (E : EnergySpace X P)
  (Pj : Projection X)
  (QW : QuadraticWithInner X P)
  (CP : ClosestPoint E Pj)
  : Set (suc (ℓx ⊔ ℓs)) where
  open QuadraticWithInner QW
  field
    Orth : X → X → Set ℓs
    orthPD : ∀ x → Orth (Projection.P Pj x) (x)

open OrthogonalityCorollary public
