module DASHI.Dynamics.MaterialFeedbackInterventionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Politics as intervention in a material feedback loop requires an explicit
-- target, mechanism, measurement, falsifier, side-effect analysis, and rollback.

data FeedbackState : Set where
  baselineState interventionApplied responseObserved rollbackApplied : FeedbackState

data InterventionAction : Set where
  applyIntervention observeResponse rollbackIntervention : InterventionAction

feedbackStep : FeedbackState → InterventionAction → FeedbackState
feedbackStep state applyIntervention = interventionApplied
feedbackStep interventionApplied observeResponse = responseObserved
feedbackStep state observeResponse = state
feedbackStep state rollbackIntervention = rollbackApplied

applyThenObserve :
  feedbackStep
    (feedbackStep baselineState applyIntervention)
    observeResponse
  ≡ responseObserved
applyThenObserve = refl

record InterventionReceipt : Set where
  constructor interventionReceipt
  field
    target : String
    mechanism : String
    expectedEffect : String
    possibleSideEffects : String
    measurement : String
    falsifier : String
    rollback : String
    provenance : String
    mechanismProved : Bool
    outcomeAchieved : Bool
    generalisesToOtherSystems : Bool

open InterventionReceipt public

candidateAdvertisingFeedbackIntervention : InterventionReceipt
candidateAdvertisingFeedbackIntervention =
  interventionReceipt
    "advertising-funded media feedback loop"
    "request advertisers to reconsider funding, altering the material revenue and reputation substrate"
    "increase accountability pressure and reduce support for the contested conduct"
    "misdirected pressure, reputational harm, entrenchment, displacement, or effects on workers and audiences"
    "document advertiser decisions, funding changes, public responses, and downstream conduct using dated provenance"
    "no material response, contrary movement, or evidence that the proposed mechanism did not mediate the change"
    "stop or revise the campaign, correct claims, restore context, and preserve an audit trail"
    "user-supplied candidate reading; disputed factual, legal, and ethical claims are not adjudicated here"
    false
    false
    false

record InterventionValidationLane : Set₁ where
  field
    Evidence State Action Outcome Score : Set
    currentState : State
    candidateAction : Action
    evidence : Evidence
    validateMechanism : Evidence → Action → Set
    predict : State → Action → Outcome
    observe : Outcome
    scorePrediction : Outcome → Outcome → Score
    adverseEffectCheck : Action → Set
    rollbackAvailable : Action → Set
    causalAttribution : Set
    generalisationReceipt : Set

record MaterialInterventionBoundary : Set where
  constructor materialInterventionBoundary
  field
    frameRecognitionMayMotivateInterventionDesign : Bool
    frameRecognitionAloneAuthorisesIntervention : Bool
    frameRecognitionAloneAuthorisesInterventionIsFalse :
      frameRecognitionAloneAuthorisesIntervention ≡ false
    interventionSuccessProvesUniqueCause : Bool
    interventionSuccessProvesUniqueCauseIsFalse :
      interventionSuccessProvesUniqueCause ≡ false
    observedAssociationProvesMechanism : Bool
    observedAssociationProvesMechanismIsFalse :
      observedAssociationProvesMechanism ≡ false
    oneCampaignGeneralisesUniversally : Bool
    oneCampaignGeneralisesUniversallyIsFalse :
      oneCampaignGeneralisesUniversally ≡ false
    measurementAndRollbackRequired : Bool
    interpretation : String

canonicalMaterialInterventionBoundary : MaterialInterventionBoundary
canonicalMaterialInterventionBoundary =
  materialInterventionBoundary
    true
    false refl
    false refl
    false refl
    false refl
    true
    "a frame-aware political hypothesis may propose a material intervention, but authority and causal attribution require target, mechanism, evidence, side-effect, measurement, falsifier, and rollback receipts"
