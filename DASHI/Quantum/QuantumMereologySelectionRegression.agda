{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySelectionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Quantum.QuantumMereologyFiniteNoMeetRegression as NoMeet
import DASHI.Quantum.QuantumMereologySelectionExact as Selection

------------------------------------------------------------------------
-- LOCAL DASHI REGRESSION THEOREMS
--
-- These are finite countermodels for the generic DASHI selection interface.
-- They are not attributed to Carroll--Singh and do not establish any empirical
-- fact about physical tensor-product structures.
------------------------------------------------------------------------

data Candidate2 : Set where
  left right : Candidate2

twoCandidateProblem :
  Selection.PreferredTPSSelectionProblem NoMeet.toyWorld
twoCandidateProblem = record
  { Selection.PreferredTPSSelectionProblem.Candidate = Candidate2
  ; Selection.PreferredTPSSelectionProblem.realizes = λ _ → NoMeet.toyTPS
  ; Selection.PreferredTPSSelectionProblem.Admissible = λ _ → ⊤
  ; Selection.PreferredTPSSelectionProblem.EntanglementGrowthScore = ⊤
  ; Selection.PreferredTPSSelectionProblem.InternalSpreadingScore = ⊤
  ; Selection.PreferredTPSSelectionProblem.entanglementGrowth = λ _ → tt
  ; Selection.PreferredTPSSelectionProblem.internalSpreading = λ _ → tt
  ; Selection.PreferredTPSSelectionProblem.NoWorse = λ _ _ → ⊤
  }

leftOptimal :
  Selection.Optimal twoCandidateProblem left
leftOptimal = tt , λ _ _ → tt

rightOptimal :
  Selection.Optimal twoCandidateProblem right
rightOptimal = tt , λ _ _ → tt

leftSelection :
  Selection.PreferredTPSSelectionReceipt twoCandidateProblem
leftSelection = record
  { Selection.PreferredTPSSelectionReceipt.selected = left
  ; Selection.PreferredTPSSelectionReceipt.selectedOptimal = leftOptimal
  }

rightSelection :
  Selection.PreferredTPSSelectionReceipt twoCandidateProblem
rightSelection = record
  { Selection.PreferredTPSSelectionReceipt.selected = right
  ; Selection.PreferredTPSSelectionReceipt.selectedOptimal = rightOptimal
  }

leftNotRight :
  left ≡ right → ⊥
leftNotRight ()

optimalityAloneDoesNotForceIdentityUniqueness :
  (authority :
    Selection.UniquePreferredTPSAuthority twoCandidateProblem) →
  ((x y : Candidate2) →
    Selection.SameTPS authority x y →
    x ≡ y) →
  ⊥
optimalityAloneDoesNotForceIdentityUniqueness authority sameReflectsEquality =
  leftNotRight
    (sameReflectsEquality
      left
      right
      (Selection.twoOptimalSelectionsAgreeGivenUniqueness
        authority leftSelection rightSelection))

------------------------------------------------------------------------
-- A criterion observer can collapse two optimal candidates that a downstream
-- consumer distinguishes. Existing consumer-descent then blocks sufficiency.
------------------------------------------------------------------------

candidateIdentityConsumer :
  Selection.CriterionConsumerSurface twoCandidateProblem
candidateIdentityConsumer = record
  { Selection.CriterionConsumerSurface.Surface = ⊤
  ; Selection.CriterionConsumerSurface.Outcome = Candidate2
  ; Selection.CriterionConsumerSurface.observeCriterion = λ _ → tt
  ; Selection.CriterionConsumerSurface.consumer = λ candidate → candidate
  }

criterionCollision :
  Selection.CriterionCollision candidateIdentityConsumer
criterionCollision = record
  { Selection.CriterionCollision.witness =
      Descent.consumerNonDescentWitness
        left
        right
        refl
        leftNotRight
  }

criterionObserverIsInsufficientForCandidateIdentity :
  Selection.CriterionConsumerSufficient candidateIdentityConsumer → ⊥
criterionObserverIsInsufficientForCandidateIdentity =
  Selection.criterionCollisionBlocksConsumerSufficiency
    criterionCollision
