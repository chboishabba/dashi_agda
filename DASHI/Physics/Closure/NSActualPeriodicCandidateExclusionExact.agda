module DASHI.Physics.Closure.NSActualPeriodicCandidateExclusionExact where

------------------------------------------------------------------------
-- RELEASED D / D14-D15 -> PERIODIC GLOBAL EXCLUSION SURFACE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicExclusionNativeExact as D

record ActualPeriodicExclusionLeaves : Set₁ where
  field
    Candidate : Set
    GlobalSolution : Set
    ClassicalSolutionTwo : Set

    restrictGlobalToTwo :
      GlobalSolution → ClassicalSolutionTwo

    candidateNoSolutionAfterOne :
      Candidate → ClassicalSolutionTwo → ⊥

open ActualPeriodicExclusionLeaves public

actualPeriodicExclusionSurface :
  ActualPeriodicExclusionLeaves →
  D.PeriodicExclusionSurface
actualPeriodicExclusionSurface L = record
  { D.Candidate = Candidate L
  ; D.GlobalSolution = GlobalSolution L
  ; D.ClassicalSolutionTwo = ClassicalSolutionTwo L
  ; D.restrictGlobalToTwo = restrictGlobalToTwo L
  ; D.candidateNoSolutionAfterOne = candidateNoSolutionAfterOne L
  }

actualPeriodicCandidateExcludesGlobalSolution :
  (L : ActualPeriodicExclusionLeaves) →
  Candidate L →
  GlobalSolution L →
  ⊥
actualPeriodicCandidateExcludesGlobalSolution L =
  D.candidateExcludesGlobalSolution (actualPeriodicExclusionSurface L)

actualPeriodicExclusionCompilerClosed : Bool
actualPeriodicExclusionCompilerClosed = true

candidateNoSolutionAfterOneAnalyticWeldInhabitedHere : Bool
candidateNoSolutionAfterOneAnalyticWeldInhabitedHere = false

globalRestrictionToTwoInhabitedHere : Bool
globalRestrictionToTwoInhabitedHere = false

actualPeriodicExclusionIntroducesPostulate : Bool
actualPeriodicExclusionIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false
