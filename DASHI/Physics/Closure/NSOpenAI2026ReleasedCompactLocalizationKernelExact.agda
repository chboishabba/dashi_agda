module DASHI.Physics.Closure.NSOpenAI2026ReleasedCompactLocalizationKernelExact where

------------------------------------------------------------------------
-- RELEASED C / PERIODIC CANDIDATE -> COMPACT R3 LOCALIZATION KERNEL
--
-- C reuses D's selected periodic candidate.  The C-specific mathematics is
-- therefore isolated here as preservation through localization:
--
--   periodic candidate
--      -> compactly supported localized velocity/pressure/force
--      -> whole-space NS residual identity
--      -> finite-energy comparison data
--      -> pre-one agreement / exclusion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact as D
import DASHI.Physics.Closure.NSOpenAI2026ReleasedR3FiniteEnergyExclusionNativeExact as CEx

record CompactLocalizationSurface
    (S : D.SelectedPeriodicCandidateSurface) : Set₁ where
  field
    PeriodicCandidate : Set
    CompactCandidate : Set
    LocalizedFields : Set

    SpatialCompactSupport : LocalizedFields → Set
    WholeSpaceNSResidualIdentity : LocalizedFields → Set
    SmoothLocalizedForce : LocalizedFields → Set
    FiniteEnergyComparisonData : LocalizedFields → Set

    localizePeriodicCandidate :
      PeriodicCandidate → LocalizedFields

    compactSupport :
      (p : PeriodicCandidate) →
      SpatialCompactSupport (localizePeriodicCandidate p)

    wholeSpaceResidualIdentity :
      (p : PeriodicCandidate) →
      WholeSpaceNSResidualIdentity (localizePeriodicCandidate p)

    localizedForceSmooth :
      (p : PeriodicCandidate) →
      SmoothLocalizedForce (localizePeriodicCandidate p)

    finiteEnergyComparisonData :
      (p : PeriodicCandidate) →
      FiniteEnergyComparisonData (localizePeriodicCandidate p)

    assembleCompactCandidate :
      (p : PeriodicCandidate) →
      SpatialCompactSupport (localizePeriodicCandidate p) →
      WholeSpaceNSResidualIdentity (localizePeriodicCandidate p) →
      SmoothLocalizedForce (localizePeriodicCandidate p) →
      FiniteEnergyComparisonData (localizePeriodicCandidate p) →
      CompactCandidate

open CompactLocalizationSurface public

localizedCompactCandidate :
  ∀ {S} →
  (L : CompactLocalizationSurface S) →
  PeriodicCandidate L →
  CompactCandidate L
localizedCompactCandidate L p =
  assembleCompactCandidate L p
    (compactSupport L p)
    (wholeSpaceResidualIdentity L p)
    (localizedForceSmooth L p)
    (finiteEnergyComparisonData L p)

record CompactCandidateExclusionCompiler
    {S : D.SelectedPeriodicCandidateSurface}
    (L : CompactLocalizationSurface S) : Set₁ where
  field
    exclusionSurface : CEx.R3FiniteEnergyExclusionSurface

    compactCandidateToExclusionCandidate :
      CompactCandidate L →
      CEx.CompactCandidate exclusionSurface

open CompactCandidateExclusionCompiler public

localizedCandidateExcludesGlobalFiniteEnergySolution :
  ∀ {S} →
  (L : CompactLocalizationSurface S) →
  (X : CompactCandidateExclusionCompiler L) →
  (p : PeriodicCandidate L) →
  CEx.GlobalFiniteEnergySolution (exclusionSurface X) →
  ⊥
localizedCandidateExcludesGlobalFiniteEnergySolution L X p global =
  CEx.compactCandidateExcludesGlobalSolution
    (exclusionSurface X)
    (compactCandidateToExclusionCandidate X (localizedCompactCandidate L p))
    global

cLocalizationAssemblyClosed : Bool
cLocalizationAssemblyClosed = true

compactSupportPreservationStillAnalytic : Bool
compactSupportPreservationStillAnalytic = true

wholeSpaceResidualIdentityStillAnalytic : Bool
wholeSpaceResidualIdentityStillAnalytic = true

wholeSpaceFiniteEnergyUniquenessStillAnalytic : Bool
wholeSpaceFiniteEnergyUniquenessStillAnalytic = true

clayPromotion : Bool
clayPromotion = false

cLocalizationAssemblyClosedIsTrue :
  cLocalizationAssemblyClosed ≡ true
cLocalizationAssemblyClosedIsTrue = refl
