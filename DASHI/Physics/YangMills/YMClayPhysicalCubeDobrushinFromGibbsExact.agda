{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayPhysicalCubeDobrushinFromGibbsExact where

------------------------------------------------------------------------
-- 2026-11-06 | R445 -> R320: original, NORMALISED conditional Gibbs
-- relative-weight influence -> same-original-row volume/cutoff-uniform
-- physical-cube influence.  Reuse the finite exact Dobrushin owners.
--
-- The logical advance is the common q across ALL selected cutoffs,
-- physical volumes, and admissible remote boundary perturbations.
-- It is NOT a postulated separate probability kernel or coarse Haar.
--
-- Inputs are explicitly a selected ORIGINAL finite fibre family and
-- proofs of its physical remote-boundary weight ratios.  Those
-- ratios and q<1 must come from the original CMP119/R445 source
-- at a fixed PHYSICAL cube scale; this module does not produce them.
-- A bare-link small-beta condition cannot inhabit this family by fiat.
--
-- This theorem gives one-cube row/observable influence, NOT spatial
-- iteration, actual CMP116 mixed-J rate, OS reconstruction or Clay.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanFiniteBoundaryConditionedDobrushinExact as Boundary
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

physicalCubeCellLength : Nat → ℚ → ℚ
physicalCubeCellLength zero spacing = 0ℚ
physicalCubeCellLength (suc cells) spacing =
  spacing + physicalCubeCellLength cells spacing

record OriginalPhysicalCubeConditionals
    (Cutoff Volume : Set)
    (Local : Cutoff → Set)
    (BoundaryState : (cutoff : Cutoff) → Volume → Set)
    (AdmissiblePerturbation :
      (cutoff : Cutoff) (volume : Volume) →
      BoundaryState cutoff volume → BoundaryState cutoff volume → Set)
    : Set₁ where
  field
    -- Same original normalized finite Gibbs family, NOT a fresh measure.
    originalFibre :
      ∀ cutoff volume →
      Boundary.BoundaryConditionedFiniteFibre
        (Local cutoff) (BoundaryState cutoff volume)

    -- Geometry in physical rather than merely lattice units.
    physicalCubeSide : ℚ
    physicalCubeSidePositive : 0ℚ < physicalCubeSide
    latticeSpacing : Cutoff → ℚ
    latticeSpacingPositive : ∀ cutoff → 0ℚ < latticeSpacing cutoff
    cubeSideInCells : Cutoff → Nat
    physicalCubeCalibration : ∀ cutoff →
      physicalCubeCellLength
        (cubeSideInCells cutoff) (latticeSpacing cutoff)
      ≡ physicalCubeSide

    -- A single strict coefficient, shared by every cutoff and volume.
    commonBlockInfluence : ℚ
    commonInfluenceNonnegative : 0ℚ ≤ commonBlockInfluence
    commonInfluenceStrict : commonBlockInfluence < 1ℚ

    -- Genuine original normalized Gibbs input from the existing owner.
    originalRawRelativeInfluence :
      ∀ cutoff volume left right →
      AdmissiblePerturbation cutoff volume left right →
      Boundary.RelativeBoundaryWeightInfluence
        (originalFibre cutoff volume) left right

    -- THE PHYSICAL ESTIMATE TO PROVE, rather than choose by definition:
    -- (2 * epsilon) <= q < 1 uniformly at fixed physical-cube size.
    actualUniformInfluenceEstimate :
      ∀ cutoff volume left right
        (perturbation :
          AdmissiblePerturbation cutoff volume left right) →
      (1ℚ + 1ℚ) * Boundary.RelativeBoundaryWeightInfluence.epsilon
        (originalRawRelativeInfluence
          cutoff volume left right perturbation)
      ≤ commonBlockInfluence

open OriginalPhysicalCubeConditionals public

-- Existing finite normalization transport now proves that the SAME
-- selected boundary-conditioned Gibbs rows are uniformly close.
originalConditionalRowsUniformlyContract :
  ∀ {Cutoff Volume Local BoundaryState AdmissiblePerturbation}
    (physical : OriginalPhysicalCubeConditionals
      Cutoff Volume Local BoundaryState AdmissiblePerturbation)
    cutoff volume left right
    (perturbation : AdmissiblePerturbation cutoff volume left right) →
  Boundary.conditionalRowL1
    (originalFibre physical cutoff volume) left right
  ≤ commonBlockInfluence physical
originalConditionalRowsUniformlyContract physical cutoff volume
    left right perturbation =
  ℚP.≤-trans
    (Boundary.relativeBoundaryInfluenceImpliesRowL1
      (originalRawRelativeInfluence physical
        cutoff volume left right perturbation))
    (actualUniformInfluenceEstimate physical
      cutoff volume left right perturbation)

-- For every bounded local observable, the ORIGINAL finite conditional
-- expectation changes by at most A q, uniformly across cutoffs/volumes.
originalConditionalObservableUniformlyContract :
  ∀ {Cutoff Volume Local BoundaryState AdmissiblePerturbation}
    (physical : OriginalPhysicalCubeConditionals
      Cutoff Volume Local BoundaryState AdmissiblePerturbation)
    cutoff volume left right
    (perturbation : AdmissiblePerturbation cutoff volume left right)
    (observable : Local cutoff → ℚ) majorant →
  0ℚ ≤ majorant →
  (∀ local → ∣ observable local ∣ ≤ majorant) →
  ∣ Boundary.conditionalExpectation
      (originalFibre physical cutoff volume) observable left
      - Boundary.conditionalExpectation
      (originalFibre physical cutoff volume) observable right ∣
  ≤ majorant * commonBlockInfluence physical
originalConditionalObservableUniformlyContract
    physical cutoff volume left right perturbation
    observable majorant majorantNN bounded =
  ℚP.≤-trans
    (Boundary.relativeBoundaryInfluenceImpliesExpectationOscillation
      (originalRawRelativeInfluence physical
        cutoff volume left right perturbation)
      observable majorant majorantNN bounded)
    (Norm.scaleNonnegative majorant majorantNN
      (actualUniformInfluenceEstimate physical
        cutoff volume left right perturbation))
