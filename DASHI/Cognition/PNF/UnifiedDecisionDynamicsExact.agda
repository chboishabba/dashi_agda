module DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch

------------------------------------------------------------------------
-- One downstream spine over the existing pre-decision owner:
--
-- stored -> accessible -> audit -> accumulator -> commitment -> actuation.
--
-- The operators remain separate.  No claim is made that one scalar utility,
-- one neural circuit, or one free-energy functional definitionally IS this
-- whole spine.
------------------------------------------------------------------------

data Accumulator : Set where
  balanced supportLead counterLead : Accumulator

data Commitment : Set where
  uncommitted supportCommitted counterCommitted : Commitment

data ActuationGate : Set where
  blocked released : ActuationGate

data ExecutedAction : Set where
  noAction supportAction counterAction : ExecutedAction

accumulate : Pre.Candidate → Accumulator → Accumulator
accumulate Pre.supportingCandidate balanced = supportLead
accumulate Pre.counterCandidate balanced = counterLead
accumulate Pre.supportingCandidate supportLead = supportLead
accumulate Pre.counterCandidate counterLead = counterLead
accumulate Pre.supportingCandidate counterLead = balanced
accumulate Pre.counterCandidate supportLead = balanced

commit : Accumulator → Commitment
commit balanced = uncommitted
commit supportLead = supportCommitted
commit counterLead = counterCommitted

actuate : ActuationGate → Commitment → ExecutedAction
actuate blocked _ = noAction
actuate released uncommitted = noAction
actuate released supportCommitted = supportAction
actuate released counterCommitted = counterAction

sameCandidateCanBeAccessibleButNotCommitted :
  Pre.accessible Pre.broadenedAccess Pre.counterCandidate ≡ true
  × commit balanced ≡ uncommitted
sameCandidateCanBeAccessibleButNotCommitted = refl , refl

commitmentCanExistWithoutActuation :
  commit counterLead ≡ counterCommitted
  × actuate blocked counterCommitted ≡ noAction
commitmentCanExistWithoutActuation = refl , refl

sameCommitmentDifferentActuation :
  actuate blocked supportCommitted
  ≡ actuate released supportCommitted → ⊥
sameCommitmentDifferentActuation ()

------------------------------------------------------------------------
-- Consideration-set truncation: changing only the live candidate set can
-- change the selected candidate even when the underlying stored carrier is
-- fixed.  This is the finite no-static-argmax witness used by the fibre layer.
------------------------------------------------------------------------

data ConsiderationMode : Set where
  narrowConsideration broadConsideration : ConsiderationMode

considered : ConsiderationMode → Pre.Candidate → Bool
considered narrowConsideration Pre.supportingCandidate = true
considered narrowConsideration Pre.counterCandidate = false
considered broadConsideration _ = true

preferredCandidate : ConsiderationMode → Pre.Candidate
preferredCandidate narrowConsideration = Pre.supportingCandidate
preferredCandidate broadConsideration = Pre.counterCandidate

storedCarrierUnchangedAcrossConsideration :
  Pre.stored Pre.counterCandidate ≡ true
storedCarrierUnchangedAcrossConsideration = refl

considerationSetCanChangePreferredCandidate :
  preferredCandidate narrowConsideration
  ≡ preferredCandidate broadConsideration → ⊥
considerationSetCanChangePreferredCandidate ()

------------------------------------------------------------------------
-- Deliberation history is a trajectory, not a static lookup.  Identical
-- eventual candidate multisets can traverse different intermediate states.
------------------------------------------------------------------------

evidenceAB : Accumulator
evidenceAB = accumulate Pre.counterCandidate
  (accumulate Pre.supportingCandidate balanced)

evidenceBA : Accumulator
evidenceBA = accumulate Pre.supportingCandidate
  (accumulate Pre.counterCandidate balanced)

-- This particular symmetric accumulator deliberately closes to the same
-- balanced endpoint: order effects are NOT built into every decision model.
-- Noncommutative update maps are supplied separately and therefore testable.
orderNeutralAccumulator : evidenceAB ≡ evidenceBA
orderNeutralAccumulator = refl

------------------------------------------------------------------------
-- Existing branch-attractor owner remains authoritative for branch quality.
------------------------------------------------------------------------

existingAdverseBranchWitness : Branch.AdverseMarginalWitness
existingAdverseBranchWitness = Branch.moreOptionsCanWorsenReachableStructure

record DecisionOperatorSeparation : Set where
  constructor decisionOperatorSeparation
  field
    accessIsCommitment : Bool
    commitmentIsActuation : Bool
    moreOptionsAlwaysImproveOutcome : Bool
    oneSelectorIsFoundational : Bool

canonicalDecisionOperatorSeparation : DecisionOperatorSeparation
canonicalDecisionOperatorSeparation =
  decisionOperatorSeparation false false false false
