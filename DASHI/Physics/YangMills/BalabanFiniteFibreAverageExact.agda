module DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational; sumRationalCong; sumRationalScale)

------------------------------------------------------------------------
-- Exact finite conditional expectation on a product of fibre labels and fibre
-- points.  The proofs are list-inductive and work for every finite side.
------------------------------------------------------------------------

sumRationalScaleRight :
  ∀ {A : Set} coefficient (values : List A) (term : A → ℚ) →
  sumRational values (λ value → term value * coefficient)
  ≡ sumRational values term * coefficient
sumRationalScaleRight coefficient [] term = ℚRing.solve-∀ coefficient
sumRationalScaleRight coefficient (value ∷ values) term
  rewrite sumRationalScaleRight coefficient values term =
  ℚRing.solve-∀ coefficient (term value) (sumRational values term)

sumRationalConstant :
  ∀ {A : Set} (values : List A) constant →
  sumRational values (λ _ → constant)
  ≡ natAsRational (length values) * constant
sumRationalConstant [] constant = ℚRing.solve-∀ constant
sumRationalConstant (value ∷ values) constant
  rewrite sumRationalConstant values constant =
  ℚRing.solve-∀ constant (natAsRational (length values))

FibreField : Set → Set → Set
FibreField Fibre Point = Fibre → Point → ℚ

fibreSum :
  ∀ {Fibre Point} → List Point → FibreField Fibre Point → Fibre → ℚ
fibreSum points field fibre = sumRational points (field fibre)

fibreAverage :
  ∀ {Fibre Point} → ℚ → List Point → FibreField Fibre Point → Fibre → ℚ
fibreAverage coefficient points field fibre =
  coefficient * fibreSum points field fibre

fibreAverageProjection :
  ∀ {Fibre Point} → ℚ → List Point →
  FibreField Fibre Point → FibreField Fibre Point
fibreAverageProjection coefficient points field fibre point =
  fibreAverage coefficient points field fibre

productInner :
  ∀ {Fibre Point} → List Fibre → List Point →
  FibreField Fibre Point → FibreField Fibre Point → ℚ
productInner fibres points left right =
  sumRational fibres
    (λ fibre →
      sumRational points
        (λ point → left fibre point * right fibre point))

fibreAverageLeftInner :
  ∀ {Fibre Point}
    coefficient (points : List Point)
    (left right : FibreField Fibre Point) fibre →
  sumRational points
    (λ point →
      fibreAverageProjection coefficient points left fibre point
      * right fibre point)
  ≡ fibreAverage coefficient points left fibre
    * fibreSum points right fibre
fibreAverageLeftInner coefficient points left right fibre =
  sumRationalScale
    (fibreAverage coefficient points left fibre)
    points
    (right fibre)

fibreAverageRightInner :
  ∀ {Fibre Point}
    coefficient (points : List Point)
    (left right : FibreField Fibre Point) fibre →
  sumRational points
    (λ point →
      left fibre point
      * fibreAverageProjection coefficient points right fibre point)
  ≡ fibreSum points left fibre
    * fibreAverage coefficient points right fibre
fibreAverageRightInner coefficient points left right fibre =
  sumRationalScaleRight
    (fibreAverage coefficient points right fibre)
    points
    (left fibre)

fibreAverageSelfAdjointPointwise :
  ∀ {Fibre Point}
    coefficient (points : List Point)
    (left right : FibreField Fibre Point) fibre →
  sumRational points
    (λ point →
      fibreAverageProjection coefficient points left fibre point
      * right fibre point)
  ≡
  sumRational points
    (λ point →
      left fibre point
      * fibreAverageProjection coefficient points right fibre point)
fibreAverageSelfAdjointPointwise coefficient points left right fibre =
  trans
    (fibreAverageLeftInner coefficient points left right fibre)
    (trans
      (ℚRing.solve-∀
        coefficient
        (fibreSum points left fibre)
        (fibreSum points right fibre))
      (symmetry
        (fibreAverageRightInner coefficient points left right fibre)))
  where
    symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
    symmetry refl = refl

finiteFibreAverageSelfAdjoint :
  ∀ {Fibre Point}
    coefficient
    (fibres : List Fibre)
    (points : List Point)
    (left right : FibreField Fibre Point) →
  productInner fibres points
    (fibreAverageProjection coefficient points left) right
  ≡ productInner fibres points left
    (fibreAverageProjection coefficient points right)
finiteFibreAverageSelfAdjoint coefficient fibres points left right =
  sumRationalCong fibres
    (λ fibre →
      sumRational points
        (λ point →
          fibreAverageProjection coefficient points left fibre point
          * right fibre point))
    (λ fibre →
      sumRational points
        (λ point →
          left fibre point
          * fibreAverageProjection coefficient points right fibre point))
    (fibreAverageSelfAdjointPointwise coefficient points left right)

fibreAverageOfProjection :
  ∀ {Fibre Point}
    coefficient (points : List Point)
    (field : FibreField Fibre Point) fibre →
  fibreAverage coefficient points
    (fibreAverageProjection coefficient points field) fibre
  ≡ coefficient * natAsRational (length points)
    * fibreAverage coefficient points field fibre
fibreAverageOfProjection coefficient points field fibre =
  trans
    (congLeft
      (sumRationalConstant points
        (fibreAverage coefficient points field fibre)))
    (ℚRing.solve-∀
      coefficient
      (natAsRational (length points))
      (fibreAverage coefficient points field fibre))
  where
    congLeft : ∀ {left right : ℚ} → left ≡ right →
      coefficient * left ≡ coefficient * right
    congLeft refl = refl

fibreAverageProjectionIdempotentPointwise :
  ∀ {Fibre Point}
    coefficient (points : List Point) →
  coefficient * natAsRational (length points) ≡ 1ℚ →
  (field : FibreField Fibre Point) fibre point →
  fibreAverageProjection coefficient points
    (fibreAverageProjection coefficient points field) fibre point
  ≡ fibreAverageProjection coefficient points field fibre point
fibreAverageProjectionIdempotentPointwise
  coefficient points normalization field fibre point =
  trans
    (fibreAverageOfProjection coefficient points field fibre)
    (trans
      (congRight normalization)
      (ℚRing.solve-∀ (fibreAverage coefficient points field fibre)))
  where
    congRight : ∀ {left right : ℚ} → left ≡ right →
      left * fibreAverage coefficient points field fibre
      ≡ right * fibreAverage coefficient points field fibre
    congRight refl = refl

finiteFibreAverageSelfAdjointnessLevel : ProofLevel
finiteFibreAverageSelfAdjointnessLevel = machineChecked

finiteFibreAverageIdempotenceLevel : ProofLevel
finiteFibreAverageIdempotenceLevel = machineChecked

physicalAxisPartitionInnerProductMatchLevel : ProofLevel
physicalAxisPartitionInnerProductMatchLevel = conditional
