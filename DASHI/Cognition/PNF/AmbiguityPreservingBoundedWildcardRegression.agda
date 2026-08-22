{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardRegression where

open import Data.Empty using (⊥)
open import DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact

------------------------------------------------------------------------
-- Endpoint agreement is not enough.
--
-- This is the finite shape of the score-interval counterexample:
--
--   A = [8,10]
--   B = [7, 9]
--
-- At the all-lower realization A beats B (8 > 7).
-- At the all-upper realization A beats B (10 > 9).
-- At the admissible mixed realization A=8, B=9, B beats A.
--
-- Therefore equality of two endpoint top-k sets does not imply invariance over
-- the full product of independently admissible score choices.
------------------------------------------------------------------------

data Candidate : Set where
  candidateA candidateB : Candidate

data Realization : Set where
  allLower mixed allUpper : Realization

data Selected : Realization → Candidate → Set where
  lowerSelectsA : Selected allLower candidateA
  mixedSelectsB : Selected mixed candidateB
  upperSelectsA : Selected allUpper candidateA

endpointLowerSelectsA : Selected allLower candidateA
endpointLowerSelectsA = lowerSelectsA

endpointUpperSelectsA : Selected allUpper candidateA
endpointUpperSelectsA = upperSelectsA

mixedDoesNotSelectA : Selected mixed candidateA → ⊥
mixedDoesNotSelectA ()

mixedSelectsDifferentCandidate : Selected mixed candidateB
mixedSelectsDifferentCandidate = mixedSelectsB

------------------------------------------------------------------------
-- Three-demand abstention witness.
--
-- The runtime receipt currently exhibits three demands whose top-k membership
-- is not certified by the interval observer.  The formal regression records the
-- semantic shape only: instability means abstention/residual, never failure or
-- fabricated negative evidence.
------------------------------------------------------------------------

data Demand : Set where
  stableDemand unstableDemand₁ unstableDemand₂ unstableDemand₃ : Demand

data NeedsAmbiguityResidual : Demand → Set where
  unstable₁ : NeedsAmbiguityResidual unstableDemand₁
  unstable₂ : NeedsAmbiguityResidual unstableDemand₂
  unstable₃ : NeedsAmbiguityResidual unstableDemand₃

unstableOneRequiresResidual : NeedsAmbiguityResidual unstableDemand₁
unstableOneRequiresResidual = unstable₁

unstableTwoRequiresResidual : NeedsAmbiguityResidual unstableDemand₂
unstableTwoRequiresResidual = unstable₂

unstableThreeRequiresResidual : NeedsAmbiguityResidual unstableDemand₃
unstableThreeRequiresResidual = unstable₃
