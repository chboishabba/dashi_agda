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
  mkEpisodeState "canonical braided episode state" Emotion.canonicalBraidedEpisode []

canonicalBraidedEmotionDynamicsBoundary : BraidedEmotionDynamicsBoundary
canonicalBraidedEmotionDynamicsBoundary =
  mkBraidedEmotionDynamicsBoundary
    canonicalEpisodeState [] true true true true true true refl
