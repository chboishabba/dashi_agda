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

open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNYuFiniteNearFieldCoercivityExact as Near

record FilteredSurplusBudget : Set where
  constructor filtered-surplus-budget
  field
    absorbedNearField : Near.AbsorbedNearFieldData
    farFieldStrain commutatorForcing localizationBudget : ℚ

open FilteredSurplusBudget public

nearFieldEnvelope : FilteredSurplusBudget → ℚ
nearFieldEnvelope budget =
  Near.retainedDiffusionCoefficient (absorbedNearField budget)
    * Near.diffusion
        (Near.coercivity (absorbedNearField budget))
  + (Near.geometricCoefficient
      (Near.coercivity (absorbedNearField budget))
      * Near.reservoirCoefficient
          (Near.coercivity (absorbedNearField budget)))
    * Near.reservoir
        (Near.coercivity (absorbedNearField budget))

totalPositiveSurplus : FilteredSurplusBudget → ℚ
totalPositiveSurplus budget =
  Near.positiveNearField
    (Near.coercivity (absorbedNearField budget))
  + farFieldStrain budget
  + commutatorForcing budget
  + localizationBudget budget

coerciveSurplusEnvelope : FilteredSurplusBudget → ℚ
coerciveSurplusEnvelope budget =
  nearFieldEnvelope budget
  + farFieldStrain budget
  + commutatorForcing budget
  + localizationBudget budget

filteredSurplusAssembly :
  (budget : FilteredSurplusBudget) →
  totalPositiveSurplus budget ≤ coerciveSurplusEnvelope budget
filteredSurplusAssembly budget =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (ℚₚ.+-mono-≤
        (Near.absorbedNearFieldCoercivity (absorbedNearField budget))
        ℚₚ.≤-refl)
      ℚₚ.≤-refl)
    ℚₚ.≤-refl
