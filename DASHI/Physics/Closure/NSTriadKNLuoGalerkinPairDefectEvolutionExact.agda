module DASHI.Physics.Closure.NSTriadKNLuoGalerkinPairDefectEvolutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- DASHI CONTRIBUTION
--
-- This module closes the finite spectral algebra of F3.  A Galerkin pair cell
-- carries two input frequencies, the polynomial defect amplitude, and the
-- exact five-source evolution
--
--   A_t + nu (lambda_L + lambda_R) A
--     = F_adv + F_stretch + F_subgrid + F_kernel + F_tail.
--
-- The pair-frequency shell theorem then gives, without using the possibly-low
-- output frequency,
--
--   A_t + 2 nu kappa A
--     <= F_adv + F_stretch + F_subgrid + F_kernel + F_tail.
--
-- The result is multiplied by nonnegative quadrature/critical weights and
-- summed recursively.  Thus the previously requested c0 2^(2q) damping is
-- mathematically available at the finite pair-frequency level.  What remains
-- original analysis is constructing these cells from the actual periodic
-- Fourier expansion and taxing the five positive source classes uniformly.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoPairFrequencyDefectDiffusionExact as Pair

record GalerkinPairDefectCell : Set where
  constructor galerkinPairDefectCell
  field
    frequencyData : Pair.PairFrequencyDefectCell
    defectRate : ℚ
    advection stretching subgrid kernel tail : ℚ
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight

    exactPairEvolution :
      defectRate + Pair.pairFrequencyDiffusion frequencyData
      ≡ advection + stretching + subgrid + kernel + tail

open GalerkinPairDefectCell public

totalPairForcing : GalerkinPairDefectCell → ℚ
totalPairForcing cell =
  advection cell + stretching cell + subgrid cell + kernel cell + tail cell

localPairDefectDampedEvolution :
  ∀ cell →
  defectRate cell + Pair.shellDefectDamping (frequencyData cell)
  ≤ totalPairForcing cell
localPairDefectDampedEvolution cell =
  let
    dampingInserted :
      defectRate cell + Pair.shellDefectDamping (frequencyData cell)
      ≤ defectRate cell + Pair.pairFrequencyDiffusion (frequencyData cell)
    dampingInserted =
      ℚₚ.+-monoʳ-≤
        (defectRate cell)
        (Pair.pairFrequencyShellDamping (frequencyData cell))
  in
  subst
    (λ upper →
      defectRate cell + Pair.shellDefectDamping (frequencyData cell)
      ≤ upper)
    (exactPairEvolution cell)
    dampingInserted

weightedDefectRate : GalerkinPairDefectCell → ℚ
weightedDefectRate cell = weight cell * defectRate cell

weightedShellDamping : GalerkinPairDefectCell → ℚ
weightedShellDamping cell =
  weight cell * Pair.shellDefectDamping (frequencyData cell)

weightedPairForcing : GalerkinPairDefectCell → ℚ
weightedPairForcing cell = weight cell * totalPairForcing cell

localWeightedPairDefectDampedEvolution :
  ∀ cell →
  weightedDefectRate cell + weightedShellDamping cell
  ≤ weightedPairForcing cell
localWeightedPairDefectDampedEvolution cell =
  let
    local = localPairDefectDampedEvolution cell

    leftValue =
      defectRate cell + Pair.shellDefectDamping (frequencyData cell)
    rightValue = totalPairForcing cell

    leftNonnegativeOrShifted :
      weight cell * leftValue ≤ weight cell * rightValue
    leftNonnegativeOrShifted =
      ℚₚ.*-monoˡ-≤-nonNeg (weight cell) local
      where
      instance
        weightNN = nonNegative (weightNonnegative cell)

    leftMeaning :
      weight cell * leftValue
      ≡ weightedDefectRate cell + weightedShellDamping cell
    leftMeaning =
      solve
        ( weight cell
        ∷ defectRate cell
        ∷ Pair.shellDefectDamping (frequencyData cell)
        ∷ [])
  in
  subst
    (λ left → left ≤ weightedPairForcing cell)
    leftMeaning
    leftNonnegativeOrShifted

sumWeightedDefectRate : List GalerkinPairDefectCell → ℚ
sumWeightedDefectRate [] = 0ℚ
sumWeightedDefectRate (cell ∷ cells) =
  weightedDefectRate cell + sumWeightedDefectRate cells

sumWeightedShellDamping : List GalerkinPairDefectCell → ℚ
sumWeightedShellDamping [] = 0ℚ
sumWeightedShellDamping (cell ∷ cells) =
  weightedShellDamping cell + sumWeightedShellDamping cells

sumWeightedPairForcing : List GalerkinPairDefectCell → ℚ
sumWeightedPairForcing [] = 0ℚ
sumWeightedPairForcing (cell ∷ cells) =
  weightedPairForcing cell + sumWeightedPairForcing cells

finiteWeightedPairDefectDampedEvolution :
  ∀ cells →
  sumWeightedDefectRate cells + sumWeightedShellDamping cells
  ≤ sumWeightedPairForcing cells
finiteWeightedPairDefectDampedEvolution [] = ℚₚ.≤-refl
finiteWeightedPairDefectDampedEvolution (cell ∷ cells) =
  let
    summed =
      ℚₚ.+-mono-≤
        (localWeightedPairDefectDampedEvolution cell)
        (finiteWeightedPairDefectDampedEvolution cells)

    leftMeaning :
      (weightedDefectRate cell + weightedShellDamping cell)
      + (sumWeightedDefectRate cells + sumWeightedShellDamping cells)
      ≡
      (weightedDefectRate cell + sumWeightedDefectRate cells)
      + (weightedShellDamping cell + sumWeightedShellDamping cells)
    leftMeaning =
      solve
        ( weightedDefectRate cell
        ∷ weightedShellDamping cell
        ∷ sumWeightedDefectRate cells
        ∷ sumWeightedShellDamping cells
        ∷ [])
  in
  subst
    (λ left → left ≤ weightedPairForcing cell + sumWeightedPairForcing cells)
    leftMeaning
    summed

record PairDefectEvolutionAuthorityBoundary : Set where
  constructor pairDefectEvolutionAuthorityBoundary
  field
    finitePairDampingFromInputFrequenciesProved : Set
    fiveSourceDampedEvolutionProved : Set
    weightedFiniteGalerkinSummationProved : Set
    actualPeriodicFourierCellsConstructed : Set
    fiveSourceCriticalTaxProduced : Set
    cutoffUniformStrictMarginProduced : Set

canonicalPairDefectEvolutionAuthorityBoundary :
  PairDefectEvolutionAuthorityBoundary
canonicalPairDefectEvolutionAuthorityBoundary =
  pairDefectEvolutionAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
