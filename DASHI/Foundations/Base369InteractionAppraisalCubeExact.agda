module DASHI.Foundations.Base369InteractionAppraisalCubeExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- The primitive relational event is not a flat trit.  It records two ordered
-- participant positions and the result computed from that ordered pair.  The
-- result then supports a six-coordinate appraisal fibre: feeling, preference
-- and synthesis stance for each participant.  The resulting one-round state
-- has nine ternary coordinates, organized as three 27-state cubes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit)

record InteractionCube : Set where
  constructor interactionCube
  field
    participantA : SSPTrit
    participantB : SSPTrit
    calculatedOutcome : SSPTrit

open InteractionCube public

record ParticipantAppraisal : Set where
  constructor participantAppraisal
  field
    feeling : SSPTrit
    preferredOutcome : SSPTrit
    synthesisStance : SSPTrit

open ParticipantAppraisal public

record AppraisalFibre : Set where
  constructor appraisalFibre
  field
    appraisalA : ParticipantAppraisal
    appraisalB : ParticipantAppraisal

open AppraisalFibre public

record OneRoundInteractionState : Set where
  constructor oneRoundInteractionState
  field
    baseInteraction : InteractionCube
    postOutcomeAppraisal : AppraisalFibre

open OneRoundInteractionState public

projectToInteraction : OneRoundInteractionState → InteractionCube
projectToInteraction = baseInteraction

fibreOver : InteractionCube → Set
fibreOver interaction = AppraisalFibre

interactionCoordinateCount : Nat
interactionCoordinateCount = 3

appraisalCoordinateCount : Nat
appraisalCoordinateCount = 6

oneRoundCoordinateCount : Nat
oneRoundCoordinateCount = 9

interactionStateCount : Nat
interactionStateCount = 3 * 3 * 3

participantAppraisalStateCount : Nat
participantAppraisalStateCount = 3 * 3 * 3

appraisalFibreStateCount : Nat
appraisalFibreStateCount = participantAppraisalStateCount * participantAppraisalStateCount

oneRoundStateCount : Nat
oneRoundStateCount = interactionStateCount * appraisalFibreStateCount

interactionStateCountIs27 : interactionStateCount ≡ 27
interactionStateCountIs27 = refl

participantAppraisalStateCountIs27 : participantAppraisalStateCount ≡ 27
participantAppraisalStateCountIs27 = refl

appraisalFibreStateCountIs729 : appraisalFibreStateCount ≡ 729
appraisalFibreStateCountIs729 = refl

oneRoundStateCountIs19683 : oneRoundStateCount ≡ 19683
oneRoundStateCountIs19683 = refl

threeCubesStateCount : Nat
threeCubesStateCount = 27 * 27 * 27

threeCubesStateCountIs19683 : threeCubesStateCount ≡ 19683
threeCubesStateCountIs19683 = refl

------------------------------------------------------------------------
-- Event completion and joint synthesis are independent observations.
------------------------------------------------------------------------

record EventAndSynthesisObservation : Set where
  constructor eventAndSynthesisObservation
  field
    eventOutcome : SSPTrit
    stanceA : SSPTrit
    stanceB : SSPTrit

open EventAndSynthesisObservation public

observeEventAndSynthesis :
  OneRoundInteractionState → EventAndSynthesisObservation
observeEventAndSynthesis state =
  eventAndSynthesisObservation
    (calculatedOutcome (baseInteraction state))
    (synthesisStance (appraisalA (postOutcomeAppraisal state)))
    (synthesisStance (appraisalB (postOutcomeAppraisal state)))

-- No theorem identifies eventOutcome with either participant's synthesis
-- stance.  Any such promotion requires an additional agreement witness.
record JointAgreementWitness (state : OneRoundInteractionState) : Set where
  constructor jointAgreementWitness
  field
    agreementA : SSPTrit
    agreementB : SSPTrit
    agreementAExact :
      synthesisStance (appraisalA (postOutcomeAppraisal state)) ≡ agreementA
    agreementBExact :
      synthesisStance (appraisalB (postOutcomeAppraisal state)) ≡ agreementB

open JointAgreementWitness public

------------------------------------------------------------------------
-- A later calculation may use the whole one-round state rather than erasing
-- the appraisal fibre to the immediate outcome.
------------------------------------------------------------------------

record SecondOrderResult : Set where
  constructor secondOrderResult
  field
    priorRound : OneRoundInteractionState
    calculatedSynthesis : SSPTrit

open SecondOrderResult public
