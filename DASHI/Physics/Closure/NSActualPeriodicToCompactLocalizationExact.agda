module DASHI.Physics.Closure.NSActualPeriodicToCompactLocalizationExact where

------------------------------------------------------------------------
-- RELEASED C / C1-C5 LEAVES -> COMPACT LOCALIZATION SURFACE
--
-- C reuses D's periodic candidate.  This owner is the concrete assembly seam:
-- compact support, the exact cutoff residual identity, smooth localized force,
-- and finite-energy comparison data compile to the existing localization
-- theorem without rebuilding the periodic construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact as D
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCompactLocalizationKernelExact as C

record ActualCompactLocalizationLeaves
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

open ActualCompactLocalizationLeaves public

actualCompactLocalizationSurface :
  ∀ {S} →
  ActualCompactLocalizationLeaves S →
  C.CompactLocalizationSurface S
actualCompactLocalizationSurface L = record
  { C.PeriodicCandidate = PeriodicCandidate L
  ; C.CompactCandidate = CompactCandidate L
  ; C.LocalizedFields = LocalizedFields L
  ; C.SpatialCompactSupport = SpatialCompactSupport L
  ; C.WholeSpaceNSResidualIdentity = WholeSpaceNSResidualIdentity L
  ; C.SmoothLocalizedForce = SmoothLocalizedForce L
  ; C.FiniteEnergyComparisonData = FiniteEnergyComparisonData L
  ; C.localizePeriodicCandidate = localizePeriodicCandidate L
  ; C.compactSupport = compactSupport L
  ; C.wholeSpaceResidualIdentity = wholeSpaceResidualIdentity L
  ; C.localizedForceSmooth = localizedForceSmooth L
  ; C.finiteEnergyComparisonData = finiteEnergyComparisonData L
  ; C.assembleCompactCandidate = assembleCompactCandidate L
  }

actualPeriodicToCompactLocalizationCompilerClosed : Bool
actualPeriodicToCompactLocalizationCompilerClosed = true

compactSupportAnalyticLeafInhabitedHere : Bool
compactSupportAnalyticLeafInhabitedHere = false

wholeSpaceResidualIdentityAnalyticLeafInhabitedHere : Bool
wholeSpaceResidualIdentityAnalyticLeafInhabitedHere = false

finiteEnergyComparisonAnalyticLeafInhabitedHere : Bool
finiteEnergyComparisonAnalyticLeafInhabitedHere = false

actualPeriodicToCompactLocalizationIntroducesPostulate : Bool
actualPeriodicToCompactLocalizationIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false
