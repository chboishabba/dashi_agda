module DASHI.Physics.Closure.NSTriadKNYuFiniteFilteredSurplusAssemblyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Implement the exact residual bookkeeping of the localized filtered
-- enstrophy balance after near-field coercivity.  Once the singular near
-- field is bounded by retained diffusion plus a lower-order reservoir, the
-- complete positive surplus is bounded by that term together with the three
-- named unresolved classes:
--
--   far-field strain;
--   differentiated commutator forcing;
--   localization/annular budgets.
--
-- This proves the modular balance and prevents near-field depletion from
-- being mistaken for complete comparable-shell closure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNYuFiniteNearFieldCoercivityExact as Near

record FilteredSurplusBudget : Set where
  constructor filtered-surplus-budget
  field
    absorbedNearField : Near.AbsorbedNearFieldData
    farFieldStrain commutatorForcing localizationBudget : ℚ

open FilteredSurplusBudget public

totalPositiveSurplus : FilteredSurplusBudget → ℚ
totalPositiveSurplus budget =
  Near.positiveNearField
    (Near.coercivity (absorbedNearField budget))
  + farFieldStrain budget
  + commutatorForcing budget
  + localizationBudget budget

coerciveSurplusEnvelope : FilteredSurplusBudget → ℚ
coerciveSurplusEnvelope budget =
  Near.retainedDiffusionCoefficient (absorbedNearField budget)
    * Near.diffusion
        (Near.coercivity (absorbedNearField budget))
  + (Near.geometricCoefficient
      (Near.coercivity (absorbedNearField budget))
      * Near.reservoirCoefficient
          (Near.coercivity (absorbedNearField budget)))
    * Near.reservoir
        (Near.coercivity (absorbedNearField budget))
  + farFieldStrain budget
  + commutatorForcing budget
  + localizationBudget budget

filteredSurplusAssembly :
  (budget : FilteredSurplusBudget) →
  totalPositiveSurplus budget ≤ coerciveSurplusEnvelope budget
filteredSurplusAssembly budget =
  let
    nearBound =
      Near.absorbedNearFieldCoercivity (absorbedNearField budget)

    firstAddition :
      Near.positiveNearField
        (Near.coercivity (absorbedNearField budget))
        + farFieldStrain budget
      ≤ (Near.retainedDiffusionCoefficient (absorbedNearField budget)
          * Near.diffusion
              (Near.coercivity (absorbedNearField budget))
        + (Near.geometricCoefficient
            (Near.coercivity (absorbedNearField budget))
            * Near.reservoirCoefficient
                (Near.coercivity (absorbedNearField budget)))
          * Near.reservoir
              (Near.coercivity (absorbedNearField budget)))
        + farFieldStrain budget
    firstAddition =
      ℚₚ.+-mono-≤ nearBound ℚₚ.≤-refl

    secondAddition =
      ℚₚ.+-mono-≤ firstAddition ℚₚ.≤-refl

    thirdAddition =
      ℚₚ.+-mono-≤ secondAddition ℚₚ.≤-refl

    targetMeaning :
      ((Near.retainedDiffusionCoefficient (absorbedNearField budget)
          * Near.diffusion
              (Near.coercivity (absorbedNearField budget))
        + (Near.geometricCoefficient
            (Near.coercivity (absorbedNearField budget))
            * Near.reservoirCoefficient
                (Near.coercivity (absorbedNearField budget)))
          * Near.reservoir
              (Near.coercivity (absorbedNearField budget)))
        + farFieldStrain budget)
        + commutatorForcing budget)
        + localizationBudget budget
      ≡ coerciveSurplusEnvelope budget
    targetMeaning =
      solve
        ( Near.retainedDiffusionCoefficient (absorbedNearField budget)
        ∷ Near.diffusion
            (Near.coercivity (absorbedNearField budget))
        ∷ Near.geometricCoefficient
            (Near.coercivity (absorbedNearField budget))
        ∷ Near.reservoirCoefficient
            (Near.coercivity (absorbedNearField budget))
        ∷ Near.reservoir
            (Near.coercivity (absorbedNearField budget))
        ∷ farFieldStrain budget
        ∷ commutatorForcing budget
        ∷ localizationBudget budget
        ∷ [])
  in
  subst
    (λ upper → totalPositiveSurplus budget ≤ upper)
    targetMeaning
    thirdAddition
