module DASHI.Physics.Closure.NSOpenAI2026ReleasedR3FiniteEnergyExclusionNativeExact where

------------------------------------------------------------------------
-- RELEASED C / NATIVE PORT OF R3FiniteEnergyComparison
--                  compact_candidate_excludes_global_solution
--
-- The whole-space proof has two genuine ingredients:
--
--   1. comparator bounded kinetic energy -> a uniform finite-energy package on
--      every compact time slab;
--   2. localized whole-space uniqueness -> agreement with the compact
--      candidate before t=1.
--
-- The compact candidate already contains the contradictory statement that no
-- such global agreement can hold.  This owner ports exactly that final proof
-- body and leaves the two analytic producers explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record R3FiniteEnergyExclusionSurface : Set₁ where
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

open R3FiniteEnergyExclusionSurface public

compactCandidateExcludesGlobalSolution :
  (S : R3FiniteEnergyExclusionSurface) →
  CompactCandidate S →
  GlobalFiniteEnergySolution S →
  ⊥
compactCandidateExcludesGlobalSolution S candidate global =
  compactCandidateForbidsGlobalAgreement S candidate
    (wholeSpaceUniquenessAgreement S candidate global
      (globalUniformFiniteEnergy S global))

releasedR3FiniteEnergyExclusionBodyPorted : Bool
releasedR3FiniteEnergyExclusionBodyPorted = true

globalFiniteEnergyExtractionConstructedHere : Bool
globalFiniteEnergyExtractionConstructedHere = false

wholeSpaceLocalizedUniquenessConstructedHere : Bool
wholeSpaceLocalizedUniquenessConstructedHere = false

clayPromotion : Bool
clayPromotion = false

releasedR3FiniteEnergyExclusionBodyPortedIsTrue :
  releasedR3FiniteEnergyExclusionBodyPorted ≡ true
releasedR3FiniteEnergyExclusionBodyPortedIsTrue = refl
