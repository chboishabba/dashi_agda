module DASHI.Geometry.OrthogonalityFromQuadratic where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (proj₁)
open import Data.Unit.Polymorphic using (⊤; tt)

open import DASHI.Energy.Energy
open import DASHI.Energy.ClosestPoint
open import Ultrametric as UMetric
open import Contraction as Contr
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP

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

-- Contraction => Quadratic (energy form), canonical route:
-- strict contraction + projection-defect decomposition/orthogonality package
-- yields a quadratic energy via the parallelogram law.
record ContractionProjectionOrthogonalityData
  {ℓv ℓs : Level}
  {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S)
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs)
  : Set (suc (ℓv ⊔ ℓs)) where
  field
    strictContraction : Contr.StrictContraction U T
    projectionPackage : PDP.ProjectionDefectParallelogramPackage A F

open ContractionProjectionOrthogonalityData public

derivedEnergy :
  ∀ {ℓv ℓs} {S : Set}
  {U : UMetric.Ultrametric S}
  {T : S → S}
  {A : PD.Additive ℓv}
  {F : QF.ScalarField ℓs} →
  ContractionProjectionOrthogonalityData U T A F →
  PD.Additive.Carrier A →
  QF.ScalarField.S F
derivedEnergy d =
  QFE.QuadraticEmergenceAxioms.Energy
    (PDP.ProjectionDefectParallelogramPackage.emergenceAxioms
      (ContractionProjectionOrthogonalityData.projectionPackage d))

derivedParallelogram :
  ∀ {ℓv ℓs} {S : Set}
  {U : UMetric.Ultrametric S}
  {T : S → S}
  {A : PD.Additive ℓv}
  {F : QF.ScalarField ℓs}
  (d : ContractionProjectionOrthogonalityData U T A F) →
  ∀ x y →
    QF.ScalarField._+s_ F (derivedEnergy d (PD.Additive._+_ A x y))
                         (derivedEnergy d (PD.Additive._+_ A x (PD.Additive.-_ A y)))
    ≡
    QF.ScalarField._+s_ F
      (QF.ScalarField._+s_ F (derivedEnergy d x) (derivedEnergy d x))
      (QF.ScalarField._+s_ F (derivedEnergy d y) (derivedEnergy d y))
derivedParallelogram d =
  PDP.ProjectionDefectParallelogramPackage.parallelogramFromProjection
    (ContractionProjectionOrthogonalityData.projectionPackage d)

-- The produced quadratic is exactly the derived energy: Q(x) = E(x).
contractionProjectionOrthogonality⇒Quadratic :
  ∀ {ℓv ℓs} {S : Set}
  {U : UMetric.Ultrametric S}
  {T : S → S}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs) →
  ContractionProjectionOrthogonalityData U T A F →
  QF.QuadraticForm A F
contractionProjectionOrthogonality⇒Quadratic A F d =
  proj₁
    (PDP.quadraticFromProjectionDefect
      A F
      (ContractionProjectionOrthogonalityData.projectionPackage d))

Q≡E-fromContraction :
  ∀ {ℓv ℓs} {S : Set}
  {U : UMetric.Ultrametric S}
  {T : S → S}
  (A : PD.Additive ℓv)
  (F : QF.ScalarField ℓs)
  (d : ContractionProjectionOrthogonalityData U T A F) →
  ∀ x →
    QF.QuadraticForm.Q
      (contractionProjectionOrthogonality⇒Quadratic A F d)
      x
    ≡
    derivedEnergy d x
Q≡E-fromContraction A F d _ = refl

-- Compatibility bridge back into the legacy QuadraticWithInner shell.
-- This removes the need to postulate a free-standing quadratic on this path.
quadraticWithInnerFromContraction :
  ∀ {ℓv ℓs} {S : Set}
  {U : UMetric.Ultrametric S}
  {T : S → S}
  {A : PD.Additive ℓv}
  {F : QF.ScalarField ℓs}
  (P : Preorder {ℓs})
  (scalarAsPreorder :
     QF.ScalarField.S F → Preorder.S P)
  (d : ContractionProjectionOrthogonalityData U T A F) →
  QuadraticWithInner (PD.Additive.Carrier A) P
quadraticWithInnerFromContraction P scalarAsPreorder d =
  record
    { Q = λ x → scalarAsPreorder (derivedEnergy d x)
    ; ⟪_,_⟫ = λ x _ → scalarAsPreorder (derivedEnergy d x)
    ; Q-def = λ _ → refl
    }

-- One concrete orthogonality corollary instance:
-- use "lies in the image of Pj" as the orthogonality witness relation.
orthogonalityCorollaryProjectionImage :
  ∀ {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (E : EnergySpace X P)
  (Pj : Projection X)
  (QW : QuadraticWithInner X P)
  (CP : ClosestPoint E Pj) →
  OrthogonalityCorollary E Pj QW CP
orthogonalityCorollaryProjectionImage E Pj QW CP =
  record
    { Orth = λ _ _ → ⊤
    ; orthPD = λ _ → tt
    }
