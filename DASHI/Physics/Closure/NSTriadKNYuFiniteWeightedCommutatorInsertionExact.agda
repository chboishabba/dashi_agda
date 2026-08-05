module DASHI.Physics.Closure.NSTriadKNYuFiniteWeightedCommutatorInsertionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Coarse-graining reference:
-- Authors: Gregory L. Eyink; Hussein Aluie.
-- Title: "Localness of energy cascade in hydrodynamic turbulence. I.
-- Smooth coarse graining".
-- DOI: 10.1063/1.3266883.
--
-- PURPOSE
-- Implement the exact finite weighted algebra of Yu's Theorem 9.3 and
-- Corollary 9.5.  At each scale,
--
--   F_com <= eta P + C_com Se(p) + L_com.
--
-- Multiplication by a nonnegative shell weight and finite summation gives the
-- weighted commutator alternative.  The differentiated cumulant estimate
-- producing the pointwise scale inequality remains a visible analytic input.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

record WeightedCommutatorCell : Set where
  constructor weighted-commutator-cell
  field
    weight forcing diffusion incrementDefect localizationBudget : ℚ
    diffusionCoefficient incrementCoefficient : ℚ

    weightNonnegative : 0ℚ ≤ weight

    commutatorInsertionBound :
      forcing
      ≤ diffusionCoefficient * diffusion
        + incrementCoefficient * incrementDefect
        + localizationBudget

open WeightedCommutatorCell public

weightedForcing : WeightedCommutatorCell → ℚ
weightedForcing cell = weight cell * forcing cell

weightedDiffusion : WeightedCommutatorCell → ℚ
weightedDiffusion cell =
  weight cell * (diffusionCoefficient cell * diffusion cell)

weightedIncrement : WeightedCommutatorCell → ℚ
weightedIncrement cell =
  weight cell * (incrementCoefficient cell * incrementDefect cell)

weightedLocalization : WeightedCommutatorCell → ℚ
weightedLocalization cell = weight cell * localizationBudget cell

weightedCellInsertion :
  (cell : WeightedCommutatorCell) →
  weightedForcing cell
  ≤ weightedDiffusion cell
    + weightedIncrement cell
    + weightedLocalization cell
weightedCellInsertion cell =
  let
    instance
      shellWeightIsNonnegative = nonNegative (weightNonnegative cell)
  in
  ℚₚ.*-monoˡ-≤-nonNeg
    (weight cell)
    (commutatorInsertionBound cell)

sumBy :
  {A : Set} →
  List A →
  (A → ℚ) →
  ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

finiteWeightedCommutatorInsertion :
  (cells : List WeightedCommutatorCell) →
  sumBy cells weightedForcing
  ≤ sumBy cells weightedDiffusion
    + sumBy cells weightedIncrement
    + sumBy cells weightedLocalization
finiteWeightedCommutatorInsertion [] = ℚₚ.≤-refl
finiteWeightedCommutatorInsertion (cell ∷ cells) =
  let
    tailBound = finiteWeightedCommutatorInsertion cells

    assembled :
      weightedForcing cell + sumBy cells weightedForcing
      ≤ (weightedDiffusion cell
          + weightedIncrement cell
          + weightedLocalization cell)
        + (sumBy cells weightedDiffusion
          + sumBy cells weightedIncrement
          + sumBy cells weightedLocalization)
    assembled =
      ℚₚ.+-mono-≤
        (weightedCellInsertion cell)
        tailBound
  in
  assembled
