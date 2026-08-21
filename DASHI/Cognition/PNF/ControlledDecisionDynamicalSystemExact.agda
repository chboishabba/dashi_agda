module DASHI.Cognition.PNF.ControlledDecisionDynamicalSystemExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Cognition.PNF.ControlledDecisionStateExact as Controlled
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics

------------------------------------------------------------------------
-- FULL CONTROLLED DECISION DYNAMICAL STATE
--
--   Z_t = (X_t, B_t, I_t, P_t, A_t, C_t, V_t, K_t,
--          Phi_t, J_t, E_t, Theta_t, H_t, M_t, Q_t, G_t, L_t)
--
-- Existing modules remain owners of each coordinate.  This module supplies the
-- product carrier and its observer projections; it does not identify any
-- projection with the complete state.
------------------------------------------------------------------------

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
  Bundle.learningState
    (Controlled.decisionState (controlledDecision state))

accessProjection : ControlledDecisionSystemState → Bool
accessProjection state =
  Bundle.accessSurface
    (Controlled.decisionState (controlledDecision state))

feelingProjection : ControlledDecisionSystemState → Embodied.FeltState
feelingProjection state = Controlled.feltState (controlledDecision state)

decisionProjection :
  ControlledDecisionSystemState → Controlled.Evidence.ThresholdCommitment
decisionProjection state = Controlled.commitmentReadout (controlledDecision state)

confidenceProjection : ControlledDecisionSystemState → Confidence.Confidence
confidenceProjection state = Controlled.confidenceReadout (controlledDecision state)

actionProjection : ControlledDecisionSystemState → Dynamics.ExecutedAction
actionProjection state = Controlled.observedAction (controlledDecision state)

potentialProjection : ControlledDecisionSystemState → _
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

canonicalControlledDecisionSystemBoundary : ControlledDecisionSystemBoundary
canonicalControlledDecisionSystemBoundary =
  controlledDecisionSystemBoundary false false false false false false true
