module DASHI.Cognition.PredictiveInverseAttractor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.FibreBraidReasoning as Reasoning
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Cognition.ReflexivePresentationFamily as Presentation

------------------------------------------------------------------------
-- Predictive inverse attraction: a represented future acts causally through
-- present action.  No backwards-in-time causal claim is made.
------------------------------------------------------------------------

record PredictiveInverseAttractor
    (State Value : Set) : Set₁ where
  field
    desiredFuture : State
    avoidedFuture : State
    previousState : State
    previousValue : Value
    expectedFuture : State
    Opposed : State → State → Set

open PredictiveInverseAttractor public

record PredictiveInverseAttractorLaw
    (State Action : Set) : Set₁ where
  field
    expectedFuture : State → State
    actionFromExpectation : State → Action
    transition : State → Action → State

open PredictiveInverseAttractorLaw public

data PerformativeResult : Set where
  selfFulfilling : PerformativeResult
  selfDefeating : PerformativeResult
  nonPerformative : PerformativeResult

record PerformativeExpectationWitness
    (State Action : Set) : Set₁ where
  field
    prediction : State
    action : Action
    outcome : State
    result : PerformativeResult

open PerformativeExpectationWitness public

------------------------------------------------------------------------
-- "Negative attractor" is a typed family of dynamical roles.
------------------------------------------------------------------------

data AttractorDynamicalRole : Set where
  repulsiveBasin : AttractorDynamicalRole
  avoidancePolicyAttractor : AttractorDynamicalRole
  predictiveAntiTarget : AttractorDynamicalRole
  negativeValenceAttractor : AttractorDynamicalRole
  complementAttractor : AttractorDynamicalRole

data AttractorValence : Set where
  negativeValence : AttractorValence
  neutralValence : AttractorValence
  positiveValence : AttractorValence

data PerformativeRole : Set where
  descriptivePerformance : PerformativeRole
  fulfillingPerformance : PerformativeRole
  defeatingPerformance : PerformativeRole

record ResolutionIndexedAttractor : Set where
  constructor resolutionIndexedAttractor
  field
    targetLabel : String
    scaleDepth : Nat
    chart : Presentation.PsychologicalChart
    contextLabel : String
    braidLabel : String
    valence : AttractorValence
    dynamicalRole : AttractorDynamicalRole
    performativeRole : PerformativeRole

open ResolutionIndexedAttractor public

------------------------------------------------------------------------
-- Optional complement symmetry.  This is stronger than mere aversion and is
-- supplied only when an involution and fixed centre are actually available.
------------------------------------------------------------------------

record ComplementedPredictiveFibre
    (Hidden Public : Set) : Set₁ where
  field
    publicProjection : Hidden → Public
    complement : Hidden → Hidden
    complementInvolutive :
      ∀ hidden → complement (complement hidden) ≡ hidden
    completionCentre : Hidden
    centreFixed : complement completionCentre ≡ completionCentre
    transition : Hidden → Hidden

open ComplementedPredictiveFibre public

swapAttractorPoles :
  Presentation.PsychologicalHiddenState →
  Presentation.PsychologicalHiddenState
swapAttractorPoles
  (Presentation.psychologicalHiddenState
    (Reasoning.reasoningState latent observed desired compelled)
    avoided remembered expected context salience confidence phase count) =
  Presentation.psychologicalHiddenState
    (Reasoning.reasoningState latent observed avoided compelled)
    desired remembered expected context salience confidence phase count

swapAttractorPolesInvolutive :
  ∀ state →
  swapAttractorPoles (swapAttractorPoles state) ≡ state
swapAttractorPolesInvolutive
  (Presentation.psychologicalHiddenState
    (Reasoning.reasoningState latent observed desired compelled)
    avoided remembered expected context salience confidence phase count) = refl

completionCentreState : Presentation.PsychologicalHiddenState
completionCentreState =
  Presentation.psychologicalHiddenState
    (Reasoning.reasoningState
      Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-mid)
    Base.tri-mid
    Phase.neutralDominant
    Phase.neutralDominant
    0
    0
    0
    Phase.phase0
    0

psychologicalComplementedFibre :
  ComplementedPredictiveFibre
    Presentation.PsychologicalHiddenState
    BT.Trit
psychologicalComplementedFibre =
  record
    { publicProjection = Presentation.balancedProjection
    ; complement = swapAttractorPoles
    ; complementInvolutive = swapAttractorPolesInvolutive
    ; completionCentre = completionCentreState
    ; centreFixed = refl
    ; transition = λ state → state
    }

canonicalAvoidanceAttractor : ResolutionIndexedAttractor
canonicalAvoidanceAttractor =
  resolutionIndexedAttractor
    "avoidance routine around anticipated threat"
    6
    Presentation.fullFibreChart
    "memory-and-context indexed"
    "memory-to-avoidance braid"
    negativeValence
    avoidancePolicyAttractor
    fulfillingPerformance
