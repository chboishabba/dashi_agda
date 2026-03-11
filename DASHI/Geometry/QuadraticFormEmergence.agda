module DASHI.Geometry.QuadraticFormEmergence where

-- Alternate/supporting quadratic emergence interface.
-- Canonical closure routing should prefer the Parallelogram -> QuadraticForm
-- spine and treat this module as non-canonical.

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
    Scale : ScalarField.S F → Additive.Carrier A → Additive.Carrier A
    ParallelogramQ :
      ∀ x y → ScalarField._+s_ F (Energy (Additive._+_ A x y))
                                  (Energy (Additive._+_ A x (Additive.-_ A y)))
              ≡ ScalarField._+s_ F (ScalarField._+s_ F (Energy x) (Energy x))
                                   (ScalarField._+s_ F (Energy y) (Energy y))
    HomogeneousQ :
      ∀ (a : ScalarField.S F) (x : Additive.Carrier A) →
        Energy (Scale a x)
          ≡
        ScalarField._*s_ F
          (ScalarField._*s_ F a a)
          (Energy x)
    Additive-On-Orth :
      ∀ x y → ProjectionDefect.Orth PD x y →
        Energy (Additive._+_ A x y) ≡
        ScalarField._+s_ F (Energy x) (Energy y)
    PD-splits : ∀ x →
      Energy x ≡
      ScalarField._+s_ F (Energy (ProjectionDefect.P PD x))
                           (Energy (ProjectionDefect.D PD x))

open QuadraticEmergenceAxioms public

QuadraticFormEmergence :
  ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
    (PD : ProjectionDefect A)
    (Ax : QuadraticEmergenceAxioms A F PD)
  → Σ (QuadraticForm A F) (λ qf → ⊤)
QuadraticFormEmergence A F PD Ax =
  let
    open QuadraticEmergenceAxioms Ax
      renaming
        ( Energy to EnergyAx
        ; Scale to ScaleAx
        ; ParallelogramQ to ParallelogramQAx
        ; HomogeneousQ to HomogeneousQAx
        )
  in
  record
    { Q = EnergyAx
    ; _·_ = ScaleAx
    ; Parallelogram = ParallelogramQAx
    ; Homog = HomogeneousQAx
    }
  , tt
