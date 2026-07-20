module DASHI.Biology.BraidedEmotionOperationalSemantics where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion
import DASHI.Biology.BraidedEmotionTheoryContention as Contention

------------------------------------------------------------------------
-- Operational relation for organism-world emotion episodes.

data Never : Set where

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → Never

data StateTag : Set where
  baselineTag : StateTag
  labelledTag : StateTag
  reappraisedTag : StateTag
  coRegulatedTag : StateTag
  recurrentTag : StateTag
  actionChangedWorldTag : StateTag

data ObservationKind : Set where
  bodilyObservation : ObservationKind
  publicLabelObservation : ObservationKind
  resistantWorldObservation : ObservationKind
  relationalObservation : ObservationKind
  changedWorldObservation : ObservationKind

data ActionKind : Set where
  attendAction : ActionKind
  provisionalLabelAction : ActionKind
  reviseInterpretationAction : ActionKind
  seekCoRegulationAction : ActionKind
  worldChangingAction : ActionKind
  recurAction : ActionKind

record OperationalState : Set where
  constructor mkOperationalState
  field
    tag : StateTag
    episode : Emotion.EmotionEpisode
    history : List String

open OperationalState public

baselineState : OperationalState
baselineState = mkOperationalState baselineTag Emotion.canonicalBraidedEpisode []

labelledState : OperationalState
labelledState =
  mkOperationalState labelledTag Emotion.canonicalBraidedEpisode
    ("a provisional label entered the episode" ∷ [])

alternativeLabelledState : OperationalState
alternativeLabelledState =
  mkOperationalState reappraisedTag Emotion.canonicalBraidedEpisode
    ("the same label was held lightly and revised by context" ∷ [])

reappraisedState : OperationalState
reappraisedState =
  mkOperationalState reappraisedTag Emotion.canonicalBraidedEpisode
    ("world resistance revised the current interpretation" ∷ [])

coRegulatedState : OperationalState
coRegulatedState =
  mkOperationalState coRegulatedTag Emotion.canonicalBraidedEpisode
    ("relation changed regulation without removing agency" ∷ [])

recurrentState : OperationalState
recurrentState =
  mkOperationalState recurrentTag Emotion.canonicalBraidedEpisode
    ("a related episode recurred without state identity" ∷ [])

changedWorldState : OperationalState
changedWorldState =
  mkOperationalState actionChangedWorldTag Emotion.canonicalBraidedEpisode
    ("action changed the later observation field" ∷ [])

infix 4 _-[_/_]→_
data _-[_/_]→_ :
  OperationalState → ObservationKind → ActionKind → OperationalState → Set where
  labelFeedbackStep :
    baselineState -[ publicLabelObservation / provisionalLabelAction ]→ labelledState
  labelFeedbackAlternativeStep :
    baselineState -[ publicLabelObservation / provisionalLabelAction ]→ alternativeLabelledState
  worldResistanceStep :
    labelledState -[ resistantWorldObservation / reviseInterpretationAction ]→ reappraisedState
  coRegulationStep :
    reappraisedState -[ relationalObservation / seekCoRegulationAction ]→ coRegulatedState
  recurrenceStep :
    coRegulatedState -[ bodilyObservation / recurAction ]→ recurrentState
  actionChangesWorldStep :
    recurrentState -[ changedWorldObservation / worldChangingAction ]→ changedWorldState

record BranchingWitness : Set where
  constructor mkBranchingWitness
  field
    source : OperationalState
    observation : ObservationKind
    action : ActionKind
    firstTarget : OperationalState
    secondTarget : OperationalState
    firstStep : source -[ observation / action ]→ firstTarget
    secondStep : source -[ observation / action ]→ secondTarget
    targetsDiffer : tag firstTarget ≢ tag secondTarget

labelledTagDiffersFromReappraisedTag : labelledTag ≢ reappraisedTag
labelledTagDiffersFromReappraisedTag ()

labelFeedbackDoesNotDetermineNextState : BranchingWitness
labelFeedbackDoesNotDetermineNextState =
  mkBranchingWitness
    baselineState
    publicLabelObservation
    provisionalLabelAction
    labelledState
    alternativeLabelledState
    labelFeedbackStep
    labelFeedbackAlternativeStep
    labelledTagDiffersFromReappraisedTag

worldResistanceCanRevisePrediction :
  labelledState -[ resistantWorldObservation / reviseInterpretationAction ]→ reappraisedState
worldResistanceCanRevisePrediction = worldResistanceStep

coRegulationPreservesAgency :
  reappraisedState -[ relationalObservation / seekCoRegulationAction ]→ coRegulatedState
coRegulationPreservesAgency = coRegulationStep

coRegulatedTagDiffersFromRecurrentTag : coRegulatedTag ≢ recurrentTag
coRegulatedTagDiffersFromRecurrentTag ()

recurrenceNeedNotBeIdentity : tag coRegulatedState ≢ tag recurrentState
recurrenceNeedNotBeIdentity = coRegulatedTagDiffersFromRecurrentTag

actionChangesFutureObservation :
  recurrentState -[ changedWorldObservation / worldChangingAction ]→ changedWorldState
actionChangesFutureObservation = actionChangesWorldStep

record TheoryProjection : Set where
  constructor mkTheoryProjection
  field
    theory : Emotion.EmotionTheory
    scale : Contention.ExplanationScale
    projectionLabel : String

open TheoryProjection public

sharedProjection : TheoryProjection
sharedProjection =
  mkTheoryProjection
    Emotion.constructionistTheory
    Contention.phenomenologicalScale
    "candidate conceptual modulation projection"

record ProjectionCollision : Set where
  constructor mkProjectionCollision
  field
    projection : TheoryProjection
    firstState : OperationalState
    secondState : OperationalState
    sameProjectionLabel : projectionLabel projection ≡ projectionLabel projection
    stateTagsDiffer : tag firstState ≢ tag secondState

noSingleProjectionReconstructsCompleteState : ProjectionCollision
noSingleProjectionReconstructsCompleteState =
  mkProjectionCollision
    sharedProjection
    labelledState
    reappraisedState
    refl
    labelledTagDiffersFromReappraisedTag
