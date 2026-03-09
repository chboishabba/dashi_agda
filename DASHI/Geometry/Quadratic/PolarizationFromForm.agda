module DASHI.Geometry.Quadratic.PolarizationFromForm where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.OrthogonalityFromPolarization as OP

-- Bridge from a quadratic form to a polarization structure.
-- This is a single seam: you supply the inner product and the identity
-- relating it to Q.
record PolarizationFromQuadratic {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F)
  : Set (suc (ℓv ⊔ ℓs)) where
  open QuadraticForm QF
  field
    pol : OP.Polarization A F
    Q-compat : ∀ x → OP.Polarization.Q pol x ≡ QuadraticForm.Q QF x

open PolarizationFromQuadratic public
