module DASHI.Physics.Closure.NSTriadKNYuFilteredGeometricDepletionSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1 (25 June 2026).
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Classical geometric reference:
-- Author: Zoran Grujic.
-- Title: "Localization and Geometric Depletion of Vortex-Stretching in the
-- 3D NSE".
-- DOI: 10.1007/s00220-008-0726-8.
--
-- PURPOSE
-- Record the exact scope of Yu's finite-scale theorem without promoting the
-- paper to a full comparable-shell closure.  The source proves a universal
-- near-field geometric estimate and a diffusion coercivity inequality at a
-- fixed relative filter scale.  It explicitly leaves three positive residual
-- classes: far-field strain, differentiated commutator forcing, and
-- localization budgets.
--
-- This is directly relevant to the comparable-shell lane because
-- ell = sigma r with fixed sigma is scale-uniform.  It is not yet an estimate
-- for the complete Littlewood--Paley CC interaction and it does not prove
-- terminal critical depletion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data StretchingRegion : Set where
  singularNearField : StretchingRegion
  nonsingularFarField : StretchingRegion

data PositiveResidualClass : Set where
  farFieldStrain : PositiveResidualClass
  differentiatedCommutator : PositiveResidualClass
  localizationBudget : PositiveResidualClass

data FilterRegime : Set where
  fixedRelativeFilter : FilterRegime
  collapsingRelativeFilter : FilterRegime

paperCoerciveRegime : FilterRegime
paperCoerciveRegime = fixedRelativeFilter

fixedAndCollapsingFilterRegimesDiffer :
  fixedRelativeFilter ≢ collapsingRelativeFilter
fixedAndCollapsingFilterRegimesDiffer ()

data ClosureLevel : Set where
  singularNearFieldClosed : ClosureLevel
  completeFilteredBalanceClosed : ClosureLevel
  completeComparableShellClosed : ClosureLevel

paperUniversalClosureLevel : ClosureLevel
paperUniversalClosureLevel = singularNearFieldClosed

nearFieldIsNotCompleteFilteredClosure :
  paperUniversalClosureLevel ≢ completeFilteredBalanceClosed
nearFieldIsNotCompleteFilteredClosure ()

nearFieldIsNotComparableShellClosure :
  paperUniversalClosureLevel ≢ completeComparableShellClosed
nearFieldIsNotComparableShellClosure ()

record FilteredNearFieldTheoremShape : Set₁ where
  field
    positiveNearFieldStretching : Set
    pairwiseDirectionDefect : Set
    filteredDiffusion : Set
    filteredEnstrophyReservoir : Set
    localEnergyBound : Set

    geometricDepletion :
      positiveNearFieldStretching → pairwiseDirectionDefect

    defectCoercivity :
      pairwiseDirectionDefect →
      filteredDiffusion →
      filteredEnstrophyReservoir →
      localEnergyBound

record CompleteFilteredBalanceObligations : Set₁ where
  field
    nearFieldStatement : Set
    farFieldStatement : Set
    commutatorStatement : Set
    localizationStatement : Set

    assemble :
      nearFieldStatement →
      farFieldStatement →
      commutatorStatement →
      localizationStatement →
      Set

-- No complete-balance inhabitant is manufactured.  Later use must provide
-- the far-field, commutator and localization producers explicitly.
