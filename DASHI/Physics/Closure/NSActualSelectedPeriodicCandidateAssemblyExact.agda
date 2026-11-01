module DASHI.Physics.Closure.NSActualSelectedPeriodicCandidateAssemblyExact where

------------------------------------------------------------------------
-- RELEASED D / D1-D6 LEAF PRODUCERS -> SELECTED PERIODIC CANDIDATE RULES
--
-- This owner turns the six concrete construction leaves into the already
-- ported SelectedPeriodicCandidateRules object.  It is deliberately
-- fail-closed: no leaf is synthesized from status flags or empirical data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Product using (_×_)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact as D

record ActualSelectedPeriodicCandidateLeaves
    (S : D.SelectedPeriodicCandidateSurface) : Set₁ where
  field
    actualSelectedAwayExtensions :
      (a : D.Schedule S) → D.AwayExtensions S a

    actualSelectedOriginBlowup :
      (a : D.Schedule S) → D.OriginBlowup S a

    actualSelectedSpatialCutDivergence :
      (a : D.Schedule S) → D.SpatialCutDivergence S a

    actualSelectedSupportData :
      (a : D.Schedule S) → D.SupportData S a

    actualSelectedVanishingResidualJets :
      (a : D.Schedule S) → D.VanishingResidualJets S a

    actualExistsCandidateForce :
      (a : D.Schedule S) →
      D.AwayExtensions S a →
      D.OriginBlowup S a →
      D.SpatialCutDivergence S a →
      D.SupportData S a →
      D.VanishingResidualJets S a →
      Σ (D.Force S) λ f → D.Candidate S f × D.SmoothForce S f

open ActualSelectedPeriodicCandidateLeaves public

actualSelectedPeriodicCandidateRules :
  ∀ {S} →
  ActualSelectedPeriodicCandidateLeaves S →
  D.SelectedPeriodicCandidateRules S
actualSelectedPeriodicCandidateRules L = record
  { D.selectedAwayExtensions = actualSelectedAwayExtensions L
  ; D.selectedOriginBlowup = actualSelectedOriginBlowup L
  ; D.selectedSpatialCutDivergence = actualSelectedSpatialCutDivergence L
  ; D.selectedSupportData = actualSelectedSupportData L
  ; D.selectedVanishingResidualJets = actualSelectedVanishingResidualJets L
  ; D.existsCandidateForce = actualExistsCandidateForce L
  }

actualSelectedPeriodicCandidate :
  ∀ {S} →
  ActualSelectedPeriodicCandidateLeaves S →
  (a : D.Schedule S) →
  Σ (D.Force S) λ f → D.Candidate S f × D.SmoothForce S f
actualSelectedPeriodicCandidate L =
  D.selectedPeriodicCandidate (actualSelectedPeriodicCandidateRules L)

actualSelectedPeriodicCandidateAssemblyCompilerClosed : Bool
actualSelectedPeriodicCandidateAssemblyCompilerClosed = true

actualSelectedAwayExtensionsInhabitedHere : Bool
actualSelectedAwayExtensionsInhabitedHere = false

actualSelectedOriginBlowupInhabitedHere : Bool
actualSelectedOriginBlowupInhabitedHere = false

actualSelectedSpatialCutDivergenceInhabitedHere : Bool
actualSelectedSpatialCutDivergenceInhabitedHere = false

actualSelectedResidualJetsInhabitedHere : Bool
actualSelectedResidualJetsInhabitedHere = false

actualSelectedPeriodicCandidateAssemblyIntroducesPostulate : Bool
actualSelectedPeriodicCandidateAssemblyIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

actualSelectedPeriodicCandidateAssemblyCompilerClosedIsTrue :
  actualSelectedPeriodicCandidateAssemblyCompilerClosed ≡ true
actualSelectedPeriodicCandidateAssemblyCompilerClosedIsTrue = refl
