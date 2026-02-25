module DASHI.Geometry.OrthogonalityFromPolarization where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm
open import DASHI.Energy.Energy
open import DASHI.Energy.ClosestPoint

-- Polarization interface: once Q is quadratic, define an inner product
-- and record the polarization identity as a seam.
record Polarization {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  : Set (suc (ℓv ⊔ ℓs)) where
  field
    Q : Additive.Carrier A → ScalarField.S F
    ⟪_,_⟫ : Additive.Carrier A → Additive.Carrier A → ScalarField.S F
    two : ScalarField.S F
    two-def : two ≡ (ScalarField._+s_ F (ScalarField.1s F) (ScalarField.1s F))
    polarization :
      ∀ x y →
        Q (Additive._+_ A x y) ≡
        ScalarField._+s_ F
          (ScalarField._+s_ F (Q x) (Q y))
          (ScalarField._*s_ F two (⟪ x , y ⟫))

open Polarization public

-- Orthogonality corollary: once closest-point is established and
-- the polarization identity is available, orthogonality becomes a target.
record OrthogonalityFromPolarization {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {P : Preorder {ℓs}}
  (ES : EnergySpace (Additive.Carrier A) P)
  (Pj : Projection (Additive.Carrier A))
  (Pol : Polarization A F)
  (CP : ClosestPoint ES Pj)
  : Set (suc (ℓv ⊔ ℓs)) where
  field
    Orth : Additive.Carrier A → Additive.Carrier A → Set ℓs
    Orth-def : ∀ x y → Orth x y ≡
      (Polarization.⟪_,_⟫ Pol x y ≡ ScalarField.0s F)
    orthPD : ∀ x →
      Orth (Projection.P Pj x)
           (Additive._+_ A x (Additive.-_ A (Projection.P Pj x)))

open OrthogonalityFromPolarization public
