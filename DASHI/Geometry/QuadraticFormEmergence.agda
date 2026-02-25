module DASHI.Geometry.QuadraticFormEmergence where

open import Level using (Level; _⊔_; suc; zero)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm

record QuadraticEmergenceAxioms {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (PD : ProjectionDefect A)
  : Set (suc (ℓv ⊔ ℓs)) where
  open Additive A
  open ScalarField F
  open ProjectionDefect PD
  field
    Energy : Additive.Carrier A → ScalarField.S F
    Additive-On-Orth :
      ∀ x y → ProjectionDefect.Orth PD x y →
        Energy (Additive._+_ A x y) ≡
        ScalarField._+s_ F (Energy x) (Energy y)
    PD-splits : ∀ x →
      Energy x ≡
      ScalarField._+s_ F (Energy (ProjectionDefect.P PD x))
                           (Energy (ProjectionDefect.D PD x))

open QuadraticEmergenceAxioms public

postulate
  QuadraticFormEmergence :
    ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
      (PD : ProjectionDefect A)
      (Ax : QuadraticEmergenceAxioms A F PD)
    → Σ (QuadraticForm A F) (λ qf → ⊤)
