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
-- paper to a full comparable-shell closure.  The source proves
--
--   V^(+,near)_(r,ell)[chi]
--     <= (3/(8 pi)) A^pair_(r,ell)[chi]
--
-- and, for every eta>0,
--
--   A^pair_(r,ell)[chi]
--     <= eta P^rho_(r,ell)[chi]
--       + (C_vartheta^2 C_varphi^2 rho^2 / eta)
--         M_(r,rho)(u) (r/ell)^5 O_(r,ell)[chi].
--
-- At a fixed relative filter ell=sigma r, the physical-scale dependence drops
-- out of the second coefficient and the remaining relative loss is sigma^-5.
-- Corollary 2.3 then absorbs the singular near field into retained diffusion
-- plus a lower-order reservoir.
--
-- The complete localized filtered balance still contains three positive
-- residual classes: far-field strain, differentiated commutator forcing, and
-- localization/annular budgets.  Hence the universal theorem closes only the
-- singular near field, not the complete Littlewood--Paley comparable class and
-- not terminal critical depletion.
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
