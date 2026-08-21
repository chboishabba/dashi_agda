module DASHI.Biology.BodyModulatedEffectiveTopologyExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DynamicEffectiveTopology as Topology
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as Cross

------------------------------------------------------------------------
-- BODY x WAVE CONTROL OF EFFECTIVE TOPOLOGY
--
-- The same anatomical edge can be open or closed under different effective
-- electrochemical/control contexts.  Body state and wave-control are kept as
-- separate coordinates; neither is claimed to be a complete neural mechanism.
------------------------------------------------------------------------

data BodyTopologyContext : Set where
  regulatedTopology mobilisedTopology : BodyTopologyContext

bodyAt : BodyTopologyContext → Body.BodyState
bodyAt regulatedTopology = Body.regulatedBody
bodyAt mobilisedTopology = Body.mobilisedBody

bodyGate : BodyTopologyContext → Bool
bodyGate regulatedTopology = true
bodyGate mobilisedTopology = false

waveGate : Cross.BetaControl → Bool
waveGate Cross.betaLow = true
waveGate Cross.betaHigh = false

combinedGate : BodyTopologyContext → Cross.BetaControl → Bool
combinedGate regulatedTopology Cross.betaLow = true
combinedGate regulatedTopology Cross.betaHigh = false
combinedGate mobilisedTopology Cross.betaLow = false
combinedGate mobilisedTopology Cross.betaHigh = false

sameWaveDifferentBodyChangesGate :
  combinedGate regulatedTopology Cross.betaLow
  ≡ combinedGate mobilisedTopology Cross.betaLow → ⊥
sameWaveDifferentBodyChangesGate ()

sameBodyDifferentWaveChangesGate :
  combinedGate regulatedTopology Cross.betaLow
  ≡ combinedGate regulatedTopology Cross.betaHigh → ⊥
sameBodyDifferentWaveChangesGate ()

effectiveState :
  BodyTopologyContext → Cross.BetaControl → Topology.ElectrochemicalState
effectiveState regulatedTopology Cross.betaLow = Topology.recurrentState
effectiveState regulatedTopology Cross.betaHigh = Topology.inhibitedState
effectiveState mobilisedTopology Cross.betaLow = Topology.inhibitedState
effectiveState mobilisedTopology Cross.betaHigh = Topology.inhibitedState

regulatedLowBetaOpensPlanningEdge :
  Topology.EffectiveEdge
    (effectiveState regulatedTopology Cross.betaLow)
    Topology.associationNode
    Topology.planningNode
regulatedLowBetaOpensPlanningEdge =
  Topology.recurrentAssociationPlanning

mobilisedSameLowBetaClosesPlanningEdge :
  Topology.EffectiveEdge
    (effectiveState mobilisedTopology Cross.betaLow)
    Topology.associationNode
    Topology.planningNode → ⊥
mobilisedSameLowBetaClosesPlanningEdge =
  Topology.inhibitedAssociationPlanningImpossible

sameAnatomyBodyStateChangesEffectiveReach :
  Topology.EffectiveEdge
    (effectiveState mobilisedTopology Cross.betaLow)
    Topology.associationNode
    Topology.planningNode → ⊥
sameAnatomyBodyStateChangesEffectiveReach =
  mobilisedSameLowBetaClosesPlanningEdge

record BodyModulatedTopologyBoundary : Set where
  constructor bodyModulatedTopologyBoundary
  field
    bodyCoordinateEqualsAnatomy : Bool
    betaCoordinateEqualsBodyState : Bool
    eitherCoordinateAloneIsUniversalMechanism : Bool
    sameAnatomyCanSupportDifferentEffectiveSubfabrics : Bool
    finiteGateProvesPhenomenalConsciousness : Bool

canonicalBodyModulatedTopologyBoundary : BodyModulatedTopologyBoundary
canonicalBodyModulatedTopologyBoundary =
  bodyModulatedTopologyBoundary false false false true false
