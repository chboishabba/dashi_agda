module DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicExclusionNativeExact where

------------------------------------------------------------------------
-- RELEASED D / NATIVE PORT OF MaximalLifespan.candidate_excludes_global_solution
--
-- The released theorem does not need an infinite-time uniqueness theorem.
-- A hypothetical global smooth periodic solution is restricted to lifespan 2;
-- the already-proved candidate_no_solution_after_one theorem then contradicts
-- the candidate's singular lifespan-one behavior.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record PeriodicExclusionSurface : Set₁ where
  field
    Candidate : Set
    GlobalSolution : Set
    ClassicalSolutionTwo : Set

    restrictGlobalToTwo :
      GlobalSolution → ClassicalSolutionTwo

    candidateNoSolutionAfterOne :
      Candidate → ClassicalSolutionTwo → ⊥

open PeriodicExclusionSurface public

candidateExcludesGlobalSolution :
  (S : PeriodicExclusionSurface) →
  Candidate S →
  GlobalSolution S →
  ⊥
candidateExcludesGlobalSolution S candidate global =
  candidateNoSolutionAfterOne S candidate
    (restrictGlobalToTwo S global)

releasedCandidateExcludesGlobalSolutionBodyPorted : Bool
releasedCandidateExcludesGlobalSolutionBodyPorted = true

periodicUniquenessNeededBelowThisTheorem : Bool
periodicUniquenessNeededBelowThisTheorem = true

candidateNoSolutionAfterOneConstructedHere : Bool
candidateNoSolutionAfterOneConstructedHere = false

globalRestrictionToTwoConstructedHere : Bool
globalRestrictionToTwoConstructedHere = false

clayPromotion : Bool
clayPromotion = false

releasedCandidateExcludesGlobalSolutionBodyPortedIsTrue :
  releasedCandidateExcludesGlobalSolutionBodyPorted ≡ true
releasedCandidateExcludesGlobalSolutionBodyPortedIsTrue = refl
