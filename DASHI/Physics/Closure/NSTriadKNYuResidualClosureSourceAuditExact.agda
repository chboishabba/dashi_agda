module DASHI.Physics.Closure.NSTriadKNYuResidualClosureSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1 (25 June 2026).
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Record the precise theorem hierarchy in Sections 8--10 of the source.
-- The paper proves unconditional finite-scale estimates and exact balance
-- reductions, but its unweighted small-scale closure remains conditional on
-- three explicit inputs:
--
-- * unweighted summability of the full far field, including an exterior tail;
-- * summability of a derivative-compatible increment defect;
-- * summability of localization and commutator-shell budgets.
--
-- This module prevents the weighted packing theorem, the reassigned annular
-- theorem, and the conditional unweighted closure theorem from being merged
-- into a single unconditional comparable-shell result.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data FarFieldResultLevel : Set where
  weightedEnergyPacking : FarFieldResultLevel
  reassignedAnnularBound : FarFieldResultLevel
  conditionalCarlesonClosure : FarFieldResultLevel
  completeExteriorTailClosure : FarFieldResultLevel

sourceUnconditionalFarFieldLevel : FarFieldResultLevel
sourceUnconditionalFarFieldLevel = reassignedAnnularBound

reassignedIsNotCompleteExteriorClosure :
  sourceUnconditionalFarFieldLevel ≢ completeExteriorTailClosure
reassignedIsNotCompleteExteriorClosure ()

data CommutatorResultLevel : Set where
  exactCumulantIdentity : CommutatorResultLevel
  derivativeIncrementEstimate : CommutatorResultLevel
  diffusionIncrementLocalizationInsertion : CommutatorResultLevel
  unconditionalIncrementSummability : CommutatorResultLevel

sourceCommutatorLevel : CommutatorResultLevel
sourceCommutatorLevel = diffusionIncrementLocalizationInsertion

insertionDoesNotSupplyIncrementSummability :
  sourceCommutatorLevel ≢ unconditionalIncrementSummability
insertionDoesNotSupplyIncrementSummability ()

data SurplusClosureLevel : Set where
  finiteWeightedSurplusInequality : SurplusClosureLevel
  conditionalUnweightedSurplusBound : SurplusClosureLevel
  conditionalVanishingDefectSurplus : SurplusClosureLevel
  unconditionalComparableShellClosure : SurplusClosureLevel

sourceStrongestClosureLevel : SurplusClosureLevel
sourceStrongestClosureLevel = conditionalVanishingDefectSurplus

conditionalVanishingIsNotUnconditionalComparableClosure :
  sourceStrongestClosureLevel ≢ unconditionalComparableShellClosure
conditionalVanishingIsNotUnconditionalComparableClosure ()

record YuUnweightedClosureInputs : Set₁ where
  field
    fullFarFieldSummable : Set
    derivativeIncrementDefectSummable : Set
    localizationBudgetsSummable : Set
    exteriorTailControlled : Set

    closeSurplus :
      fullFarFieldSummable →
      derivativeIncrementDefectSummable →
      localizationBudgetsSummable →
      exteriorTailControlled →
      Set

-- No inhabitant of YuUnweightedClosureInputs is manufactured from energy.
-- Any promotion to a complete CC theorem must construct all four fields.
