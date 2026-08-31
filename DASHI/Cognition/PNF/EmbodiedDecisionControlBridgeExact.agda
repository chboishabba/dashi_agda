module DASHI.Cognition.PNF.EmbodiedDecisionControlBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Access
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact as Threshold

record DecisionControlSurface : Set where
  constructor decisionControlSurface
  field
    accessMode : Access.AccessMode
    thresholdPolicy : Threshold.ThresholdPolicy
    potentialContext : Potential.Context
    confidenceCandidate : Confidence.Confidence

open DecisionControlSurface public

controlFromFeeling : Embodied.FeltState → DecisionControlSurface
controlFromFeeling Embodied.settledFeeling =
  decisionControlSurface Access.broadenedAccess Threshold.lowerThreshold
    Potential.ordinaryContext Confidence.highConfidence
controlFromFeeling Embodied.activatedFeeling =
  decisionControlSurface Access.broadenedAccess Threshold.lowerThreshold
    Potential.ordinaryContext Confidence.highConfidence
controlFromFeeling Embodied.alarmedFeeling =
  decisionControlSurface Access.narrowedAccess Threshold.elevatedThreshold
    Potential.threatContext Confidence.lowConfidence

feltFromBody : Embodied.InteroceptivePrior → Embodied.BodyState → Embodied.FeltState
feltFromBody prior body =
  Embodied.inferFeltState prior (Embodied.afference body)

bodyToDecisionControl :
  Embodied.InteroceptivePrior → Embodied.BodyState → DecisionControlSurface
bodyToDecisionControl prior body = controlFromFeeling (feltFromBody prior body)

sameMobilisedBodyDifferentPriorChangesControl :
  accessMode (bodyToDecisionControl Embodied.safetyPrior Embodied.mobilisedBody)
  ≡ accessMode (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody) → ⊥
sameMobilisedBodyDifferentPriorChangesControl ()

sameMobilisedBodyDifferentPriorChangesThreshold :
  thresholdPolicy (bodyToDecisionControl Embodied.safetyPrior Embodied.mobilisedBody)
  ≡ thresholdPolicy (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody) → ⊥
sameMobilisedBodyDifferentPriorChangesThreshold ()

sameMobilisedBodyDifferentPriorChangesPotential :
  potentialContext (bodyToDecisionControl Embodied.safetyPrior Embodied.mobilisedBody)
  ≡ potentialContext (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody) → ⊥
sameMobilisedBodyDifferentPriorChangesPotential ()

sameMobilisedBodyDifferentPriorChangesConfidenceCandidate :
  confidenceCandidate (bodyToDecisionControl Embodied.safetyPrior Embodied.mobilisedBody)
  ≡ confidenceCandidate (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody) → ⊥
sameMobilisedBodyDifferentPriorChangesConfidenceCandidate ()

interoceptiveControlIsMultiAxis :
  accessMode (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody)
    ≡ Access.narrowedAccess
  × thresholdPolicy (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody)
    ≡ Threshold.elevatedThreshold
  × potentialContext (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody)
    ≡ Potential.threatContext
  × confidenceCandidate (bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody)
    ≡ Confidence.lowConfidence
interoceptiveControlIsMultiAxis = refl , (refl , (refl , refl))

record EmbodiedDecisionControlBoundary : Set where
  constructor embodiedDecisionControlBoundary
  field
    bodyEqualsFeltState : Bool
    feltStateEqualsDecision : Bool
    oneBodyCoordinateDeterminesAllControl : Bool
    interoceptiveStateMayParticipateInMultipleControlAxes : Bool

canonicalEmbodiedDecisionControlBoundary : EmbodiedDecisionControlBoundary
canonicalEmbodiedDecisionControlBoundary =
  embodiedDecisionControlBoundary false false false true
