module DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre

------------------------------------------------------------------------
-- Literature calibration:
-- Jerome R. Busemeyer; James T. Townsend,
-- "Decision Field Theory: A Dynamic-Cognitive Approach to Decision Making in
-- an Uncertain Environment", DOI 10.1037/0033-295X.100.3.432.
--
-- This is a finite exact decision-field producer, not a reproduction of the
-- stochastic differential equations in the paper.  It captures only the
-- load-bearing structure needed by the unified DASHI spine: time-indexed
-- preference, contextual valence, and pairwise competition.
------------------------------------------------------------------------

data PreferenceState : Set where
  balanced supportAhead counterAhead : PreferenceState

data EvidencePulse : Set where
  supportPulse counterPulse : EvidencePulse

data Interaction : Set where
  reinforcing interfering independent : Interaction

updatePreference : EvidencePulse → PreferenceState → PreferenceState
updatePreference supportPulse balanced = supportAhead
updatePreference counterPulse balanced = counterAhead
updatePreference supportPulse supportAhead = supportAhead
updatePreference counterPulse counterAhead = counterAhead
updatePreference supportPulse counterAhead = balanced
updatePreference counterPulse supportAhead = balanced

candidateInteraction : Pre.Candidate → Pre.Candidate → Interaction
candidateInteraction Pre.supportingCandidate Pre.counterCandidate = interfering
candidateInteraction Pre.counterCandidate Pre.supportingCandidate = interfering
candidateInteraction c₁ c₂ = independent

sameInitialStateDifferentPulse :
  updatePreference supportPulse balanced
  ≡ updatePreference counterPulse balanced → ⊥
sameInitialStateDifferentPulse ()

competingCandidatesInterfere :
  candidateInteraction Pre.supportingCandidate Pre.counterCandidate ≡ interfering
competingCandidatesInterfere = refl

------------------------------------------------------------------------
-- Time pressure / horizon can expose an early preference that later evidence
-- reverses without any change to the candidate identities.
------------------------------------------------------------------------

earlyState : PreferenceState
earlyState = updatePreference supportPulse balanced

laterState : PreferenceState
laterState = updatePreference counterPulse
  (updatePreference counterPulse earlyState)

earlyPreference : earlyState ≡ supportAhead
earlyPreference = refl

laterPreference : laterState ≡ counterAhead
laterPreference = refl

preferenceCanReverseOverTrajectory : earlyState ≡ laterState → ⊥
preferenceCanReverseOverTrajectory ()

record DynamicDecisionFieldBoundary : Set where
  constructor dynamicDecisionFieldBoundary
  field
    preferenceIsStaticUtilityLookup : Bool
    onePulseDeterminesPermanentPreference : Bool
    competitionIsAlwaysAdditive : Bool

canonicalDynamicDecisionFieldBoundary : DynamicDecisionFieldBoundary
canonicalDynamicDecisionFieldBoundary =
  dynamicDecisionFieldBoundary false false false
