module DASHI.Physics.Closure.NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
-- Close the exact finite shell-summation step after per-shell integrated
-- absorption.  Nonnegative Sobolev/shell weights transport
--
--   T_q <= eta V_q + R_q
--
-- into the weighted finite sum, and the remaining viscosity coefficient is
-- exposed exactly as (1-eta).  This is the algebra consumed by a weighted
-- energy estimate; it does not prove the physical per-shell producer or the
-- infinite-series limit.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record AbsorptionParameters : Set where
  constructor absorptionParameters
  field
    eta : ℚ
    etaNonnegative : 0ℚ ≤ eta
    oneMinusEtaNonnegative : 0ℚ ≤ 1ℚ - eta

open AbsorptionParameters public

record WeightedShellCell (parameters : AbsorptionParameters) : Set where
  constructor weightedShellCell
  field
    weight transfer viscosity residual : ℚ
    weightNonnegative : 0ℚ ≤ weight
    transferNonnegative : 0ℚ ≤ transfer
    viscosityNonnegative : 0ℚ ≤ viscosity
    residualNonnegative : 0ℚ ≤ residual
    shellAbsorption : transfer ≤ eta parameters * viscosity + residual

open WeightedShellCell public

etaTimesViscosityNonnegative :
  ∀ {parameters} (cell : WeightedShellCell parameters) →
  0ℚ ≤ eta parameters * viscosity cell
etaTimesViscosityNonnegative {parameters} cell =
  let
    instance
      etaNN = nonNegative (etaNonnegative parameters)
      viscosityNN = nonNegative (viscosityNonnegative cell)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (eta parameters) (viscosity cell)
  in
  ℚₚ.nonNegative⁻¹ (eta parameters * viscosity cell)

localWeightedAbsorption :
  ∀ {parameters} (cell : WeightedShellCell parameters) →
  weight cell * transfer cell
  ≤ eta parameters * (weight cell * viscosity cell)
    + weight cell * residual cell
localWeightedAbsorption {parameters} cell =
  let
    upperNonnegative :
      0ℚ ≤ eta parameters * viscosity cell + residual cell
    upperNonnegative =
      L2.addNonnegative
        (etaTimesViscosityNonnegative cell)
        (residualNonnegative cell)

    scaled :
      weight cell * transfer cell
      ≤ weight cell * (eta parameters * viscosity cell + residual cell)
    scaled =
      L2.nonnegativeProductMonotone
        (weightNonnegative cell)
        (transferNonnegative cell)
        (weightNonnegative cell)
        upperNonnegative
        ℚₚ.≤-refl
        (shellAbsorption cell)

    factorized :
      weight cell * (eta parameters * viscosity cell + residual cell)
      ≡ eta parameters * (weight cell * viscosity cell)
        + weight cell * residual cell
    factorized =
      solve
        ( weight cell
        ∷ eta parameters
        ∷ viscosity cell
        ∷ residual cell
        ∷ [])
  in
  subst
    (λ upper → weight cell * transfer cell ≤ upper)
    factorized
    scaled

weightedTransfer :
  ∀ {parameters} → List (WeightedShellCell parameters) → ℚ
weightedTransfer [] = 0ℚ
weightedTransfer (cell ∷ cells) =
  weight cell * transfer cell + weightedTransfer cells

weightedViscosity :
  ∀ {parameters} → List (WeightedShellCell parameters) → ℚ
weightedViscosity [] = 0ℚ
weightedViscosity (cell ∷ cells) =
  weight cell * viscosity cell + weightedViscosity cells

weightedResidual :
  ∀ {parameters} → List (WeightedShellCell parameters) → ℚ
weightedResidual [] = 0ℚ
weightedResidual (cell ∷ cells) =
  weight cell * residual cell + weightedResidual cells

weightedAbsorptionSummation :
  ∀ {parameters} (cells : List (WeightedShellCell parameters)) →
  weightedTransfer cells
  ≤ eta parameters * weightedViscosity cells + weightedResidual cells
weightedAbsorptionSummation [] = ℚₚ.≤-refl
weightedAbsorptionSummation {parameters} (cell ∷ cells) =
  let
    local = localWeightedAbsorption cell
    tail = weightedAbsorptionSummation cells
    summed = ℚₚ.+-mono-≤ local tail

    rearranged :
      ( eta parameters * (weight cell * viscosity cell)
        + weight cell * residual cell
      )
      +
      ( eta parameters * weightedViscosity cells
        + weightedResidual cells
      )
      ≡
      eta parameters
        * (weight cell * viscosity cell + weightedViscosity cells)
      +
      (weight cell * residual cell + weightedResidual cells)
    rearranged =
      solve
        ( eta parameters
        ∷ weight cell
        ∷ viscosity cell
        ∷ residual cell
        ∷ weightedViscosity cells
        ∷ weightedResidual cells
        ∷ [])
  in
  subst
    (λ upper →
      weight cell * transfer cell + weightedTransfer cells ≤ upper)
    rearranged
    summed

strictViscosityMargin :
  ∀ {parameters} (cells : List (WeightedShellCell parameters)) →
  (1ℚ - eta parameters) * weightedViscosity cells
    + weightedTransfer cells
  ≤ weightedViscosity cells + weightedResidual cells
strictViscosityMargin {parameters} cells =
  let
    absorbed = weightedAbsorptionSummation cells
    shifted =
      ℚₚ.+-mono-≤
        ℚₚ.≤-refl
        absorbed

    closed :
      (1ℚ - eta parameters) * weightedViscosity cells
      +
      (eta parameters * weightedViscosity cells + weightedResidual cells)
      ≡ weightedViscosity cells + weightedResidual cells
    closed =
      solve
        (eta parameters ∷ weightedViscosity cells
          ∷ weightedResidual cells ∷ [])
  in
  subst
    (λ upper →
      (1ℚ - eta parameters) * weightedViscosity cells
        + weightedTransfer cells
      ≤ upper)
    closed
    shifted

record WeightedAbsorptionBoundary : Set where
  constructor weightedAbsorptionBoundary
  field
    finiteWeightedSumProvesInfiniteSobolevSummability : Set
    finiteWeightedSumDoesNotProveInfiniteSobolevSummability :
      finiteWeightedSumProvesInfiniteSobolevSummability → Set

    absorptionAlgebraProvesResidenceCompression : Set
    absorptionAlgebraDoesNotProveResidenceCompression :
      absorptionAlgebraProvesResidenceCompression → Set

canonicalWeightedAbsorptionBoundary : WeightedAbsorptionBoundary
canonicalWeightedAbsorptionBoundary =
  weightedAbsorptionBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
