module DASHI.Physics.Plasma.IdealMHDReconnectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Physics.Plasma.MagneticTopologyHyperfabricExact as Plasma

------------------------------------------------------------------------
-- IDEAL-MHD / RECONNECTION BIDI KERNEL
--
-- Source-shaped physics boundary:
-- ideal-MHD frozen-in evolution preserves field-line connectivity; magnetic
-- reconnection requires a non-ideal mechanism that breaks frozen-in evolution,
-- changes topology, and permits conversion of magnetic energy into plasma
-- kinetic/thermal/particle energy.
------------------------------------------------------------------------

data PlasmaEvolutionRegime : Set where
  idealMHD
  resistiveMHD
  hallOrTwoFluid
  collisionlessKinetic
  : PlasmaEvolutionRegime

data TopologyMove : Set where
  advectFrozenFlux
  reconnectFieldLines
  : TopologyMove

record ReconnectionState : Set₁ where
  constructor reconnection-state
  field
    voxel : Plasma.PlasmaHypervoxel
    TopologyBefore TopologyAfter : Set
    MagneticEnergyBefore PlasmaEnergyAfter : Set
    stateReference : String

open ReconnectionState public

record ReconnectionEnablement
    (regime : PlasmaEvolutionRegime)
    (state : ReconnectionState) : Set where
  constructor reconnection-enablement
  field
    NonIdealTermPresent : Set
    FrozenInConditionBroken : Set
    topologyMayChange : Set
    enablementReference : String

open ReconnectionEnablement public

record ReconnectionReceipt
    (regime : PlasmaEvolutionRegime)
    (state : ReconnectionState) : Set where
  constructor reconnection-receipt
  field
    enablement : ReconnectionEnablement regime state
    topologyActuallyChanges : Set
    magneticEnergyConversion : Set
    receiptReference : String

open ReconnectionReceipt public

------------------------------------------------------------------------
-- Transition-system cross-pollination.
------------------------------------------------------------------------

record ReconnectionTransitionSocket : Set₁ where
  constructor reconnection-transition-socket
  field
    system : Transition.AdmissibleTransitionSystem
    stateEmbedding : ReconnectionState → Transition.State system
    regimeEmbedding : PlasmaEvolutionRegime → Transition.Parameter system
    moveEmbedding : TopologyMove → Transition.Move system

    idealFrozenInDisablesReconnection :
      (state : ReconnectionState) →
      Transition.Enabled system
        (moveEmbedding reconnectFieldLines)
        (regimeEmbedding idealMHD)
        (stateEmbedding state) → ⊥

    nonIdealReceiptEnablesReconnection :
      (regime : PlasmaEvolutionRegime) →
      (state : ReconnectionState) →
      ReconnectionEnablement regime state →
      Transition.Enabled system
        (moveEmbedding reconnectFieldLines)
        (regimeEmbedding regime)
        (stateEmbedding state)

    transitionReference : String

open ReconnectionTransitionSocket public

------------------------------------------------------------------------
-- BIDI direction.
-- Forward: non-ideal local physics can authorize a topology-changing move.
-- Reverse: observed topology change asks for a producer of frozen-in breaking;
-- topology change itself does not identify the unique microphysical mechanism.
------------------------------------------------------------------------

record ReconnectionBidiBoundary : Set where
  constructor reconnection-bidi-boundary
  field
    idealMHDPermitsTopologyChangingReconnectionByDefinition : Bool
    idealMHDPermitsTopologyChangingReconnectionByDefinitionIsFalse :
      idealMHDPermitsTopologyChangingReconnectionByDefinition ≡ false

    topologyChangeRequiresNonIdealProducer : Bool
    topologyChangeRequiresNonIdealProducerIsTrue :
      topologyChangeRequiresNonIdealProducer ≡ true

    topologyChangeUniquelyIdentifiesMicrophysics : Bool
    topologyChangeUniquelyIdentifiesMicrophysicsIsFalse :
      topologyChangeUniquelyIdentifiesMicrophysics ≡ false

    reconnectionIsFusion : Bool
    reconnectionIsFusionIsFalse : reconnectionIsFusion ≡ false

    reconnectionIsFRC : Bool
    reconnectionIsFRCIsFalse : reconnectionIsFRC ≡ false

canonicalReconnectionBidiBoundary : ReconnectionBidiBoundary
canonicalReconnectionBidiBoundary =
  reconnection-bidi-boundary false refl true refl false refl false refl false refl
