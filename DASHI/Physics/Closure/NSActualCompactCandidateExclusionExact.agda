module DASHI.Physics.Closure.NSActualCompactCandidateExclusionExact where

------------------------------------------------------------------------
-- RELEASED C / C6-C8 LEAVES -> R3 FINITE-ENERGY EXCLUSION SURFACE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedR3FiniteEnergyExclusionNativeExact as C

record ActualR3FiniteEnergyExclusionLeaves : Set₁ where
  field
    CompactCandidate : Set
    GlobalFiniteEnergySolution : Set
    UniformFiniteEnergyOnCompactSlabs : Set
    PreOneAgreement : Set

    globalUniformFiniteEnergy :
      GlobalFiniteEnergySolution →
      UniformFiniteEnergyOnCompactSlabs

    wholeSpaceUniquenessAgreement :
      CompactCandidate →
      GlobalFiniteEnergySolution →
      UniformFiniteEnergyOnCompactSlabs →
      PreOneAgreement

    compactCandidateForbidsGlobalAgreement :
      CompactCandidate →
      PreOneAgreement →
      ⊥

open ActualR3FiniteEnergyExclusionLeaves public

actualR3FiniteEnergyExclusionSurface :
  ActualR3FiniteEnergyExclusionLeaves →
  C.R3FiniteEnergyExclusionSurface
actualR3FiniteEnergyExclusionSurface L = record
  { C.CompactCandidate = CompactCandidate L
  ; C.GlobalFiniteEnergySolution = GlobalFiniteEnergySolution L
  ; C.UniformFiniteEnergyOnCompactSlabs =
      UniformFiniteEnergyOnCompactSlabs L
  ; C.PreOneAgreement = PreOneAgreement L
  ; C.globalUniformFiniteEnergy = globalUniformFiniteEnergy L
  ; C.wholeSpaceUniquenessAgreement = wholeSpaceUniquenessAgreement L
  ; C.compactCandidateForbidsGlobalAgreement =
      compactCandidateForbidsGlobalAgreement L
  }

actualCompactCandidateExclusionCompilerClosed : Bool
actualCompactCandidateExclusionCompilerClosed = true

globalFiniteEnergyExtractionAnalyticLeafInhabitedHere : Bool
globalFiniteEnergyExtractionAnalyticLeafInhabitedHere = false

wholeSpaceLocalizedUniquenessAnalyticLeafInhabitedHere : Bool
wholeSpaceLocalizedUniquenessAnalyticLeafInhabitedHere = false

actualCompactCandidateExclusionIntroducesPostulate : Bool
actualCompactCandidateExclusionIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

actualCompactCandidateExclusionCompilerClosedIsTrue :
  actualCompactCandidateExclusionCompilerClosed ≡ true
actualCompactCandidateExclusionCompilerClosedIsTrue = refl
