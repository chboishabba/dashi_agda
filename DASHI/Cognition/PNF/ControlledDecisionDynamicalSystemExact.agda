module DASHI.Cognition.PNF.ControlledDecisionDynamicalSystemExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence
import DASHI.Cognition.PNF.ControlledDecisionStateExact as Controlled
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics

record ControlledDecisionSystemState : Set where
  constructor controlledDecisionSystemState
  field
    controlledDecision : Controlled.ControlledDecisionState
    allostaticBody : Allostatic.AllostaticBodyState
    landscapePosition : Landscape.LandscapeState
    allostaticCoreMatchesDecisionBody :
      Allostatic.autonomicEndocrineCore allostaticBody
      ≡ Controlled.bodyState controlledDecision

open ControlledDecisionSystemState public

memoryProjection : ControlledDecisionSystemState → Memory.MemoryFibre
memoryProjection state =
  Bundle.learningState (Controlled.decisionState (controlledDecision state))

accessProjection : ControlledDecisionSystemState → Bool
accessProjection state =
  Bundle.accessSurface (Controlled.decisionState (controlledDecision state))

feelingProjection : ControlledDecisionSystemState → Embodied.FeltState
feelingProjection state = Controlled.feltState (controlledDecision state)

decisionProjection : ControlledDecisionSystemState → Evidence.ThresholdCommitment
decisionProjection state = Controlled.commitmentReadout (controlledDecision state)

confidenceProjection : ControlledDecisionSystemState → Confidence.Confidence
confidenceProjection state = Controlled.confidenceReadout (controlledDecision state)

actionProjection : ControlledDecisionSystemState → Dynamics.ExecutedAction
actionProjection state = Controlled.observedAction (controlledDecision state)

potentialProjection : ControlledDecisionSystemState → Nat
potentialProjection state = Landscape.potential (landscapePosition state)

fluxProjection : ControlledDecisionSystemState → Landscape.FluxRegime
fluxProjection state = Controlled.fluxRegime (controlledDecision state)

nextLandscapePosition : ControlledDecisionSystemState → Landscape.LandscapeState
nextLandscapePosition state =
  Landscape.next (fluxProjection state) (landscapePosition state)

canonicalSystemState :
  (memory : Memory.MemoryFibre) → ControlledDecisionSystemState
canonicalSystemState memory =
  controlledDecisionSystemState
    (Controlled.canonicalControlled memory Confidence.highConfidence)
    Allostatic.regulatedExtended
    Landscape.leftMinimum
    refl

------------------------------------------------------------------------
-- Explicit controlled transition: Z_{t+1} = T(Z_t, u_t, o_t).
-- The finite input controls landscape flow while an observation token is kept
-- separately typed.  This first exact transition is intentionally conservative:
-- it changes one dynamical coordinate and proves unrelated decision projections
-- stay fixed, providing a base for richer coupled updates without conflation.
------------------------------------------------------------------------

data ControlInput : Set where
  holdLandscape : ControlInput
  applyClockwiseFlux applyCounterclockwiseFlux : ControlInput

data ExternalObservation : Set where
  noExternalObservation : ExternalObservation

inputFlux : ControlInput → Landscape.FluxRegime
inputFlux holdLandscape = Landscape.noFlux
inputFlux applyClockwiseFlux = Landscape.clockwiseFlux
inputFlux applyCounterclockwiseFlux = Landscape.counterclockwiseFlux

transition :
  ControlledDecisionSystemState →
  ControlInput →
  ExternalObservation →
  ControlledDecisionSystemState
transition state input observation =
  controlledDecisionSystemState
    (controlledDecision state)
    (allostaticBody state)
    (Landscape.next (inputFlux input) (landscapePosition state))
    (allostaticCoreMatchesDecisionBody state)

transitionPreservesMemory :
  (state : ControlledDecisionSystemState)
  (input : ControlInput)
  (observation : ExternalObservation) →
  memoryProjection (transition state input observation) ≡ memoryProjection state
transitionPreservesMemory state input observation = refl

transitionPreservesAccess :
  (state : ControlledDecisionSystemState)
  (input : ControlInput)
  (observation : ExternalObservation) →
  accessProjection (transition state input observation) ≡ accessProjection state
transitionPreservesAccess state input observation = refl

transitionPreservesDecisionReadout :
  (state : ControlledDecisionSystemState)
  (input : ControlInput)
  (observation : ExternalObservation) →
  decisionProjection (transition state input observation) ≡ decisionProjection state
transitionPreservesDecisionReadout state input observation = refl

transitionPreservesAction :
  (state : ControlledDecisionSystemState)
  (input : ControlInput)
  (observation : ExternalObservation) →
  actionProjection (transition state input observation) ≡ actionProjection state
transitionPreservesAction state input observation = refl

clockwiseInputMovesCanonicalLandscape :
  (memory : Memory.MemoryFibre) →
  landscapePosition
    (transition (canonicalSystemState memory)
      applyClockwiseFlux noExternalObservation)
  ≡ Landscape.saddle
clockwiseInputMovesCanonicalLandscape memory = refl

counterclockwiseInputMovesCanonicalLandscapeDifferently :
  (memory : Memory.MemoryFibre) →
  landscapePosition
    (transition (canonicalSystemState memory)
      applyCounterclockwiseFlux noExternalObservation)
  ≡ Landscape.rightMinimum
counterclockwiseInputMovesCanonicalLandscapeDifferently memory = refl

record ControlledDecisionSystemBoundary : Set where
  constructor controlledDecisionSystemBoundary
  field
    memoryProjectionIsWholeState : Bool
    feelingProjectionIsWholeState : Bool
    decisionProjectionIsWholeState : Bool
    confidenceProjectionIsWholeState : Bool
    actionProjectionIsWholeState : Bool
    landscapePotentialIsWholeDynamics : Bool
    explicitMultiProjectionCarrierExists : Bool
    explicitControlledTransitionExists : Bool

canonicalControlledDecisionSystemBoundary : ControlledDecisionSystemBoundary
canonicalControlledDecisionSystemBoundary =
  controlledDecisionSystemBoundary false false false false false false true true
