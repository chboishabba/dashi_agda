module DASHI.Physics.Closure.NSTriadKNLuoFiveSourceDefectCriticalTaxExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact F4 taxation algebra for the five sources
-- produced by the polynomial pair-defect evolution:
--
--   advection, stretching, subgrid, kernel, tail.
--
-- Every source is bounded in the admissible form
--
--   F_i <= eta_i D + A_i + B_i X_int.
--
-- Recursive finite addition is replaced here by a fixed, named five-source
-- theorem so no source can disappear into a generic remainder.  The result is
--
--   sum F_i
--     <= eta_total D + A_total + B_total X_int.
--
-- Combined with an integrated defect balance, this yields
--
--   A_out + (1-eta_total)D
--     <= A_in + A_total + B_total X_int.
--
-- The remaining frontier is producing the five source taxes from actual
-- periodic Navier-Stokes with eta_total strictly below one.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

record SourceCriticalTax (diffusion integratedCritical : ℚ) : Set where
  constructor sourceCriticalTax
  field
    forcing eta additive linear : ℚ
    tax :
      forcing
      ≤ eta * diffusion + additive + linear * integratedCritical

open SourceCriticalTax public

record FiveSourceCriticalTaxData : Set where
  constructor fiveSourceCriticalTaxData
  field
    diffusion integratedCritical : ℚ
    advectionTax stretchingTax subgridTax kernelTax tailTax :
      SourceCriticalTax diffusion integratedCritical

open FiveSourceCriticalTaxData public

totalForcing : FiveSourceCriticalTaxData → ℚ
totalForcing dataSet =
  forcing (advectionTax dataSet)
  + forcing (stretchingTax dataSet)
  + forcing (subgridTax dataSet)
  + forcing (kernelTax dataSet)
  + forcing (tailTax dataSet)

totalEta : FiveSourceCriticalTaxData → ℚ
totalEta dataSet =
  eta (advectionTax dataSet)
  + eta (stretchingTax dataSet)
  + eta (subgridTax dataSet)
  + eta (kernelTax dataSet)
  + eta (tailTax dataSet)

totalAdditive : FiveSourceCriticalTaxData → ℚ
totalAdditive dataSet =
  additive (advectionTax dataSet)
  + additive (stretchingTax dataSet)
  + additive (subgridTax dataSet)
  + additive (kernelTax dataSet)
  + additive (tailTax dataSet)

totalLinear : FiveSourceCriticalTaxData → ℚ
totalLinear dataSet =
  linear (advectionTax dataSet)
  + linear (stretchingTax dataSet)
  + linear (subgridTax dataSet)
  + linear (kernelTax dataSet)
  + linear (tailTax dataSet)

fiveSourceCriticalTax :
  ∀ dataSet →
  totalForcing dataSet
  ≤ totalEta dataSet * diffusion dataSet
    + totalAdditive dataSet
    + totalLinear dataSet * integratedCritical dataSet
fiveSourceCriticalTax dataSet =
  let
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (ℚₚ.+-mono-≤
              (tax (advectionTax dataSet))
              (tax (stretchingTax dataSet)))
            (tax (subgridTax dataSet)))
          (tax (kernelTax dataSet)))
        (tax (tailTax dataSet))

    rightMeaning :
      (eta (advectionTax dataSet) * diffusion dataSet
        + additive (advectionTax dataSet)
        + linear (advectionTax dataSet) * integratedCritical dataSet)
      + (eta (stretchingTax dataSet) * diffusion dataSet
        + additive (stretchingTax dataSet)
        + linear (stretchingTax dataSet) * integratedCritical dataSet)
      + (eta (subgridTax dataSet) * diffusion dataSet
        + additive (subgridTax dataSet)
        + linear (subgridTax dataSet) * integratedCritical dataSet)
      + (eta (kernelTax dataSet) * diffusion dataSet
        + additive (kernelTax dataSet)
        + linear (kernelTax dataSet) * integratedCritical dataSet)
      + (eta (tailTax dataSet) * diffusion dataSet
        + additive (tailTax dataSet)
        + linear (tailTax dataSet) * integratedCritical dataSet)
      ≡
      totalEta dataSet * diffusion dataSet
        + totalAdditive dataSet
        + totalLinear dataSet * integratedCritical dataSet
    rightMeaning =
      solve
        ( diffusion dataSet ∷ integratedCritical dataSet
        ∷ eta (advectionTax dataSet)
        ∷ eta (stretchingTax dataSet)
        ∷ eta (subgridTax dataSet)
        ∷ eta (kernelTax dataSet)
        ∷ eta (tailTax dataSet)
        ∷ additive (advectionTax dataSet)
        ∷ additive (stretchingTax dataSet)
        ∷ additive (subgridTax dataSet)
        ∷ additive (kernelTax dataSet)
        ∷ additive (tailTax dataSet)
        ∷ linear (advectionTax dataSet)
        ∷ linear (stretchingTax dataSet)
        ∷ linear (subgridTax dataSet)
        ∷ linear (kernelTax dataSet)
        ∷ linear (tailTax dataSet)
        ∷ [])
  in
  subst
    (λ upper → totalForcing dataSet ≤ upper)
    rightMeaning
    summed

record IntegratedFiveSourceDefectBudget : Set where
  constructor integratedFiveSourceDefectBudget
  field
    taxData : FiveSourceCriticalTaxData
    defectIn defectOut : ℚ

    integratedDefectBalance :
      defectOut + diffusion taxData
      ≤ defectIn + totalForcing taxData

open IntegratedFiveSourceDefectBudget public

remainingDefectDamping : IntegratedFiveSourceDefectBudget → ℚ
remainingDefectDamping budget = 1ℚ - totalEta (taxData budget)

fiveSourceDefectAbsorption :
  ∀ budget →
  defectOut budget
    + remainingDefectDamping budget * diffusion (taxData budget)
  ≤
  defectIn budget
    + totalAdditive (taxData budget)
    + totalLinear (taxData budget)
      * integratedCritical (taxData budget)
fiveSourceDefectAbsorption budget =
  let
    dataSet = taxData budget

    inserted :
      defectIn budget + totalForcing dataSet
      ≤
      defectIn budget
        + (totalEta dataSet * diffusion dataSet
          + totalAdditive dataSet
          + totalLinear dataSet * integratedCritical dataSet)
    inserted =
      ℚₚ.+-monoʳ-≤ (defectIn budget) (fiveSourceCriticalTax dataSet)

    assembled :
      defectOut budget + diffusion dataSet
      ≤
      defectIn budget
        + (totalEta dataSet * diffusion dataSet
          + totalAdditive dataSet
          + totalLinear dataSet * integratedCritical dataSet)
    assembled =
      ℚₚ.≤-trans (integratedDefectBalance budget) inserted

    shift = - (totalEta dataSet * diffusion dataSet)
    shifted = ℚₚ.+-monoʳ-≤ shift assembled

    leftMeaning :
      (defectOut budget + diffusion dataSet) + shift
      ≡ defectOut budget
        + remainingDefectDamping budget * diffusion dataSet
    leftMeaning =
      solve
        ( defectOut budget
        ∷ diffusion dataSet
        ∷ totalEta dataSet
        ∷ [])

    rightMeaning :
      (defectIn budget
        + (totalEta dataSet * diffusion dataSet
          + totalAdditive dataSet
          + totalLinear dataSet * integratedCritical dataSet))
      + shift
      ≡
      defectIn budget
        + totalAdditive dataSet
        + totalLinear dataSet * integratedCritical dataSet
    rightMeaning =
      solve
        ( defectIn budget
        ∷ diffusion dataSet
        ∷ totalEta dataSet
        ∷ totalAdditive dataSet
        ∷ totalLinear dataSet
        ∷ integratedCritical dataSet
        ∷ [])
  in
  subst
    (λ left →
      left
      ≤ defectIn budget
        + totalAdditive dataSet
        + totalLinear dataSet * integratedCritical dataSet)
    leftMeaning
    (subst
      (λ right →
        (defectOut budget + diffusion dataSet) + shift ≤ right)
      rightMeaning
      shifted)

record FiveSourceTaxAuthorityBoundary : Set where
  constructor fiveSourceTaxAuthorityBoundary
  field
    namedFiveSourceTaxAlgebraProved : Set
    integratedDefectAbsorptionProved : Set
    advectionPhysicalTaxProduced : Set
    stretchingPhysicalTaxProduced : Set
    subgridPhysicalTaxProduced : Set
    kernelPhysicalTaxProduced : Set
    tailPhysicalTaxProduced : Set
    strictFiveSourceEtaProduced : Set

canonicalFiveSourceTaxAuthorityBoundary : FiveSourceTaxAuthorityBoundary
canonicalFiveSourceTaxAuthorityBoundary =
  fiveSourceTaxAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
