module DASHI.Cognition.PNF.ConsiderationSetSelectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics

------------------------------------------------------------------------
-- Literature calibration:
-- John R. Hauser; Birger Wernerfelt,
-- "An Evaluation Cost Model of Consideration Sets",
-- Journal of Consumer Research 16(4) (1990), DOI 10.1086/209225.
--
-- A bounded evaluator may optimize coherently over a strict live subset of the
-- stored carrier.  Local optimality on that subset is not global
-- option-completeness.
------------------------------------------------------------------------

candidateValue : Pre.Candidate → Nat
candidateValue Pre.supportingCandidate = 1
candidateValue Pre.counterCandidate = 2

selectedByValue : Dynamics.ConsiderationMode → Pre.Candidate
selectedByValue Dynamics.narrowConsideration = Pre.supportingCandidate
selectedByValue Dynamics.broadConsideration = Pre.counterCandidate

narrowSelectionIsLive :
  Dynamics.considered Dynamics.narrowConsideration
    (selectedByValue Dynamics.narrowConsideration) ≡ true
narrowSelectionIsLive = refl

broadSelectionIsLive :
  Dynamics.considered Dynamics.broadConsideration
    (selectedByValue Dynamics.broadConsideration) ≡ true
broadSelectionIsLive = refl

counterHasHigherStoredValue :
  candidateValue Pre.counterCandidate ≡ 2
  × candidateValue Pre.supportingCandidate ≡ 1
counterHasHigherStoredValue = refl , refl

higherValueCandidateCanBeExcludedFromLiveSet :
  candidateValue Pre.counterCandidate ≡ 2
  × Dynamics.considered Dynamics.narrowConsideration Pre.counterCandidate ≡ false
higherValueCandidateCanBeExcludedFromLiveSet = refl , refl

localAndFullCarrierOptimaCanDiffer :
  selectedByValue Dynamics.narrowConsideration
  ≡ selectedByValue Dynamics.broadConsideration → ⊥
localAndFullCarrierOptimaCanDiffer ()

storedCarrierStillContainsExcludedCandidate :
  Pre.stored Pre.counterCandidate ≡ true
storedCarrierStillContainsExcludedCandidate = refl

record ConsiderationSetSelectionBoundary : Set where
  constructor considerationSetSelectionBoundary
  field
    localOptimalityImpliesFullCarrierOptimality : Bool
    excludedCandidateIsDeletedFromStorage : Bool
    selectionErrorEqualsValuationError : Bool

canonicalConsiderationSetSelectionBoundary : ConsiderationSetSelectionBoundary
canonicalConsiderationSetSelectionBoundary =
  considerationSetSelectionBoundary false false false
