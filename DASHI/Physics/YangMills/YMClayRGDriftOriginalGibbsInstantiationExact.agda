{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRGDriftOriginalGibbsInstantiationExact where

------------------------------------------------------------------------
-- R445 -> R320: derive a common physical-cube Gibbs Dobrushin q from
-- a reference-stage coefficient plus ALL original UV refinement drifts.
--
-- No caller chooses q in this constructor; q is definitionally
-- referenceInfluence + uniformTotalRGErrorBudget.
--
-- The two genuine selected physical leaves, which are NOT axioms:
--   1. each original R445 normalized conditional TV influence is
--      bounded by its actual scale-indexed weighted coefficient;
--   2. original RG adjacent-scale drifts have a summable uniform
--      error budget (in YMClayPhysicalRGDriftToUniformInfluenceExact).
--
-- Retains exact source-block physical side a(n)*cells(n)=ell;
-- no synthetic Haar, Gibbs, measure, CMP116, or OS carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanFiniteBoundaryConditionedDobrushinExact as Boundary
import DASHI.Physics.YangMills.YMClayPhysicalCubeDobrushinFromGibbsExact as Cube
import DASHI.Physics.YangMills.YMClayPhysicalRGDriftToUniformInfluenceExact as RG

record SelectedOriginalGibbsRGComparison
    (Volume : Set)
    (Local : Nat → Set)
    (BoundaryState : Nat → Volume → Set)
    (AdmissiblePerturbation :
      (stage : Nat) (volume : Volume) →
      BoundaryState stage volume → BoundaryState stage volume → Set)
    (rg : RG.SelectedPhysicalRGInfluenceBudget) : Set₁ where
  field
    -- Physical cells count at EVERY UV refinement, same ell as RG.
    latticeSpacing : Nat → ℚ
    latticeSpacingPositive : ∀ stage → 0ℚ < latticeSpacing stage
    physicalCubeCellCount : Nat → Nat
    fixedPhysicalCubeCalibration :
      ∀ stage →
      Cube.physicalCubeCellLength
        (physicalCubeCellCount stage) (latticeSpacing stage)
      ≡ RG.actualPhysicalCubeSide rg

    actualOriginalGibbsConditional :
      ∀ stage volume →
      Boundary.BoundaryConditionedFiniteFibre
        (Local stage) (BoundaryState stage volume)

    actualOriginalRelativeWeightInfluence :
      ∀ stage volume left right →
      AdmissiblePerturbation stage volume left right →
      Boundary.RelativeBoundaryWeightInfluence
        (actualOriginalGibbsConditional stage volume) left right

    -- This is a TRUE physical comparison to source-normalized Gibbs
    -- conditional row, not an artificial bound on a chosen toy Markov
    -- matrix. The input MUST be proved from the original CMP119/R445
    -- Wilson weight and actual physical cube boundary algebra.
    realOriginalConditionalInfluenceUpper :
      ∀ stage volume left right
        (perturbation : AdmissiblePerturbation stage volume left right) →
      (1ℚ + 1ℚ) *
        Boundary.RelativeBoundaryWeightInfluence.epsilon
          (actualOriginalRelativeWeightInfluence
            stage volume left right perturbation)
      ≤ RG.selectedPhysicalInfluence rg stage

    combinedCoefficientNonnegative :
      0ℚ ≤
        RG.referenceInfluence rg
          + RG.uniformTotalRGErrorBudget rg

open SelectedOriginalGibbsRGComparison public

-- The requested cutoff/volume uniform bound is now CALCULATED rather
-- than an independent input field: q = q0 + sum RG perturbations.
-- Quantitative validity still requires actual source proofs in the
-- constructor's two inputs.
originalPhysicalCubeFromRGDrift :
  ∀ {Volume Local BoundaryState AdmissiblePerturbation}
    {rg : RG.SelectedPhysicalRGInfluenceBudget} →
  SelectedOriginalGibbsRGComparison
    Volume Local BoundaryState AdmissiblePerturbation rg →
  Cube.OriginalPhysicalCubeConditionals
    Nat Volume Local BoundaryState AdmissiblePerturbation
originalPhysicalCubeFromRGDrift {rg = rg} physical = record
  { Cube.OriginalPhysicalCubeConditionals.originalFibre =
      actualOriginalGibbsConditional physical
  ; Cube.OriginalPhysicalCubeConditionals.physicalCubeSide =
      RG.actualPhysicalCubeSide rg
  ; Cube.OriginalPhysicalCubeConditionals.physicalCubeSidePositive =
      RG.actualPhysicalCubeSidePositive rg
  ; Cube.OriginalPhysicalCubeConditionals.latticeSpacing =
      latticeSpacing physical
  ; Cube.OriginalPhysicalCubeConditionals.latticeSpacingPositive =
      latticeSpacingPositive physical
  ; Cube.OriginalPhysicalCubeConditionals.cubeSideInCells =
      physicalCubeCellCount physical
  ; Cube.OriginalPhysicalCubeConditionals.physicalCubeCalibration =
      fixedPhysicalCubeCalibration physical
  ; Cube.OriginalPhysicalCubeConditionals.commonBlockInfluence =
      RG.referenceInfluence rg
        + RG.uniformTotalRGErrorBudget rg
  ; Cube.OriginalPhysicalCubeConditionals.commonInfluenceNonnegative =
      combinedCoefficientNonnegative physical
  ; Cube.OriginalPhysicalCubeConditionals.commonInfluenceStrict =
      RG.selectedRGInfluenceUniformStrictMargin rg
  ; Cube.OriginalPhysicalCubeConditionals.originalRawRelativeInfluence =
      actualOriginalRelativeWeightInfluence physical
  ; Cube.OriginalPhysicalCubeConditionals.actualUniformInfluenceEstimate =
      λ stage volume left right perturbation →
        ℚP.≤-trans
          (realOriginalConditionalInfluenceUpper physical
            stage volume left right perturbation)
          (RG.selectedRGInfluenceUniformPhysicalUpper rg stage)
  }
