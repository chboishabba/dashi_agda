module DASHI.Biology.BraidedEmotionDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion

data EpisodeUpdateKind : Set where
  accumulationUpdate : EpisodeUpdateKind
  escalationUpdate : EpisodeUpdateKind
  decayUpdate : EpisodeUpdateKind
  interruptionUpdate : EpisodeUpdateKind
  coRegulationUpdate : EpisodeUpdateKind
  reappraisalUpdate : EpisodeUpdateKind
  labelFeedbackUpdate : EpisodeUpdateKind
  actionWorldUpdate : EpisodeUpdateKind
  worldResistanceUpdate : EpisodeUpdateKind
  recurrenceUpdate : EpisodeUpdateKind

record EpisodeState : Set where
  constructor mkEpisodeState
  field
    stateLabel : String
    episode : Emotion.EmotionEpisode
    activeUpdates : List EpisodeUpdateKind

record EpisodeTransition : Set where
  constructor mkEpisodeTransition
  field
    source : EpisodeState
    update : EpisodeUpdateKind
    target : EpisodeState
    actionChangesWorld : Bool
    worldCanResistPrediction : Bool
    labelCanFeedBack : Bool
    relationCanCoRegulate : Bool

record BraidedEmotionDynamicsBoundary : Set where
  constructor mkBraidedEmotionDynamicsBoundary
  field
    initialState : EpisodeState
    transitions : List EpisodeTransition
    noDeterministicEmotionEssence : Bool
    noLabelOnlyTransitionLaw : Bool
    worldResistancePreserved : Bool
    coRegulationPreserved : Bool
    recurrenceAllowed : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open EpisodeState public
open EpisodeTransition public
open BraidedEmotionDynamicsBoundary public

canonicalEpisodeState : EpisodeState
canonicalEpisodeState =
  mkEpisodeState
    "canonical braided episode state"
    Emotion.canonicalBraidedEpisode
    []

labelFeedbackState : EpisodeState
labelFeedbackState =
  mkEpisodeState
    "candidate label feeds back without becoming episode identity"
    Emotion.canonicalBraidedEpisode
    (labelFeedbackUpdate ∷ [])

worldResistanceState : EpisodeState
worldResistanceState =
  mkEpisodeState
    "world evidence resists and revises the current interpretation"
    Emotion.canonicalBraidedEpisode
    (worldResistanceUpdate ∷ reappraisalUpdate ∷ [])

coRegulatedState : EpisodeState
coRegulatedState =
  mkEpisodeState
    "relation changes regulation while agency remains available"
    Emotion.canonicalBraidedEpisode
    (coRegulationUpdate ∷ decayUpdate ∷ [])

recurrentState : EpisodeState
recurrentState =
  mkEpisodeState
    "a recurrent episode is related to but not identified with its predecessor"
    Emotion.canonicalBraidedEpisode
    (recurrenceUpdate ∷ accumulationUpdate ∷ [])

canonicalLabelFeedbackTransition : EpisodeTransition
canonicalLabelFeedbackTransition =
  mkEpisodeTransition
    canonicalEpisodeState
    labelFeedbackUpdate
    labelFeedbackState
    false
    true
    true
    true

canonicalWorldResistanceTransition : EpisodeTransition
canonicalWorldResistanceTransition =
  mkEpisodeTransition
    labelFeedbackState
    worldResistanceUpdate
    worldResistanceState
    true
    true
    true
    true

canonicalCoRegulationTransition : EpisodeTransition
canonicalCoRegulationTransition =
  mkEpisodeTransition
    worldResistanceState
    coRegulationUpdate
    coRegulatedState
    true
    true
    true
    true

canonicalRecurrenceTransition : EpisodeTransition
canonicalRecurrenceTransition =
  mkEpisodeTransition
    coRegulatedState
    recurrenceUpdate
    recurrentState
    true
    true
    true
    true

canonicalEpisodeTransitions : List EpisodeTransition
canonicalEpisodeTransitions =
  canonicalLabelFeedbackTransition
  ∷ canonicalWorldResistanceTransition
  ∷ canonicalCoRegulationTransition
  ∷ canonicalRecurrenceTransition
  ∷ []

canonicalBraidedEmotionDynamicsBoundary : BraidedEmotionDynamicsBoundary
canonicalBraidedEmotionDynamicsBoundary =
  mkBraidedEmotionDynamicsBoundary
    canonicalEpisodeState
    canonicalEpisodeTransitions
    true
    true
    true
    true
    true
    true
    refl

canonicalTransitionsAreInstantiated :
  transitions canonicalBraidedEmotionDynamicsBoundary ≡ canonicalEpisodeTransitions
canonicalTransitionsAreInstantiated = refl
