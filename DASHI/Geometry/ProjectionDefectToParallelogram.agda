module DASHI.Geometry.ProjectionDefectToParallelogram where

-- Canonical quadratic emergence path anchor:
-- ProjectionDefect -> Parallelogram -> QuadraticForm.
--
-- Alternative derivations (QuadraticFromNorm, QuadraticEmergence,
-- QuadraticFormEmergence) are retained for validation/experiments and should
-- not be imported by Stage-C closure pipeline modules.

open import Level using (Level; _⊔_; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE

record ProjectionDefectParallelogramPackage
  {ℓv ℓs : Level}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs) : Set (suc (ℓv ⊔ ℓs)) where
  field
    projection : PD.ProjectionDefect A
    emergenceAxioms : QFE.QuadraticEmergenceAxioms A F projection
    parallelogramFromProjection :
      ∀ x y →
        QF.ScalarField._+s_ F
          (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms
            (PD.Additive._+_ A x y))
          (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms
            (PD.Additive._+_ A x (PD.Additive.-_ A y)))
        ≡
        QF.ScalarField._+s_ F
          (QF.ScalarField._+s_ F
            (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms x)
            (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms x))
          (QF.ScalarField._+s_ F
            (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms y)
            (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms y))
    splitEnergyOnProjectionDefect :
      ∀ x →
        QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms x
        ≡
        QF.ScalarField._+s_ F
          (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms
            (PD.ProjectionDefect.P projection x))
          (QFE.QuadraticEmergenceAxioms.Energy emergenceAxioms
            (PD.ProjectionDefect.D projection x))

fromEmergenceAxioms :
  ∀ {ℓv ℓs}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs)
  (Proj : PD.ProjectionDefect A)
  (Ax : QFE.QuadraticEmergenceAxioms A F Proj) →
  ProjectionDefectParallelogramPackage A F
fromEmergenceAxioms A F Proj Ax =
  record
    { projection = Proj
    ; emergenceAxioms = Ax
    ; parallelogramFromProjection =
        QFE.QuadraticEmergenceAxioms.ParallelogramQ Ax
    ; splitEnergyOnProjectionDefect =
        QFE.QuadraticEmergenceAxioms.PD-splits Ax
    }

quadraticFromProjectionDefect :
  ∀ {ℓv ℓs}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs)
  (Pkg : ProjectionDefectParallelogramPackage A F) →
  Σ (QF.QuadraticForm A F) (λ _ → ⊤)
quadraticFromProjectionDefect A F Pkg =
  QFE.QuadraticFormEmergence A F
    (ProjectionDefectParallelogramPackage.projection Pkg)
    (ProjectionDefectParallelogramPackage.emergenceAxioms Pkg)

record ProjectionDefectQuadraticWitness
  {ℓv ℓs : Level}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs) : Set (suc (ℓv ⊔ ℓs)) where
  field
    package : ProjectionDefectParallelogramPackage A F
    quadratic : QF.QuadraticForm A F
    witnessToken : ⊤

fromProjectionPackageWitness :
  ∀ {ℓv ℓs}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs)
  (Pkg : ProjectionDefectParallelogramPackage A F) →
  ProjectionDefectQuadraticWitness A F
fromProjectionPackageWitness A F Pkg =
  record
    { package = Pkg
    ; quadratic = proj₁ (quadraticFromProjectionDefect A F Pkg)
    ; witnessToken = proj₂ (quadraticFromProjectionDefect A F Pkg)
    }
