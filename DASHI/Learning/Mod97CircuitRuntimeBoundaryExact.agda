module DASHI.Learning.Mod97CircuitRuntimeBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Runtime implementation, execution, historical identity, leakage, topology,
-- and scientific payment are deliberately different carriers.
------------------------------------------------------------------------

data ProducerStatus : Set where
  missing : ProducerStatus
  implemented : ProducerStatus

data ExecutionStatus : Set where
  notExecuted : ExecutionStatus
  executed : ExecutionStatus

data IdentityStatus : Set where
  notEstablished : IdentityStatus
  established : IdentityStatus

data SelectionLeakageStatus : Set where
  heldOutNotUsedForSelection : SelectionLeakageStatus
  heldOutUsedForSelection : SelectionLeakageStatus

data RequirementDirectionStatus : Set where
  unavailableForCurrentTopology : RequirementDirectionStatus
  externallyPayable : RequirementDirectionStatus

data PaymentStatus : Set where
  unpaid : PaymentStatus
  paid : PaymentStatus

record Mod97CircuitRuntimeFrontier : Set where
  constructor mod97CircuitRuntimeFrontier
  field
    checkpointProducer : ProducerStatus
    checkpointExecution : ExecutionStatus
    interventionProducer : ProducerStatus
    interventionExecution : ExecutionStatus
    historicalRunIdentity : IdentityStatus
    historicalConfigurationIdentity : IdentityStatus
    selectionLeakage : SelectionLeakageStatus
    natDamageAdapterPayment : PaymentStatus
    requirementDirectionStatus : RequirementDirectionStatus
    requirementEdgePayment : PaymentStatus
    relationClassificationPayment : PaymentStatus
    betaMaximalityPayment : PaymentStatus
    mechanismPayment : PaymentStatus
open Mod97CircuitRuntimeFrontier public

------------------------------------------------------------------------
-- Current exact frontier on PR #900.
--
-- The checked-in Python producers implement a new-run checkpoint path and a
-- training-selected / held-out-evaluated raw intervention path. Raw signed
-- held-out loss changes are retained, while an orientation-aware adapter maps
-- only positive loss increase into non-negative micro-loss Nat damage. That
-- representation payment is distinct from relation classification.
--
-- The current intervention producer acts on parallel post-ReLU units in one
-- hidden layer. There is no hidden-unit -> hidden-unit edge in that runtime
-- topology, so same-layer singleton/joint ablations cannot pay directional
-- requirement evidence. A different externally paid topology/intervention
-- receipt would be needed before gluing-requirement direction can be promoted.
-- No numerical run receipt has yet been observed here, and the historical
-- receipt does not pay exact original architecture/split identity.
------------------------------------------------------------------------

currentMod97RuntimeFrontier : Mod97CircuitRuntimeFrontier
currentMod97RuntimeFrontier =
  mod97CircuitRuntimeFrontier
    implemented
    notExecuted
    implemented
    notExecuted
    notEstablished
    notEstablished
    heldOutNotUsedForSelection
    paid
    unavailableForCurrentTopology
    unpaid
    unpaid
    unpaid
    unpaid

------------------------------------------------------------------------
-- Explicit non-promotion witnesses.
------------------------------------------------------------------------

producerImplementationPaysExecution : PaymentStatus
producerImplementationPaysExecution = unpaid

natDamageAdapterPaysRequirementEdges : PaymentStatus
natDamageAdapterPaysRequirementEdges = unpaid

natDamageAdapterPaysRelationClassification : PaymentStatus
natDamageAdapterPaysRelationClassification = unpaid

sameLayerPostReluAblationPaysRequirementDirection : PaymentStatus
sameLayerPostReluAblationPaysRequirementDirection = unpaid

rawInterventionPaysRequirementEdges : PaymentStatus
rawInterventionPaysRequirementEdges = unpaid

rawInterventionPaysRelationClassification : PaymentStatus
rawInterventionPaysRelationClassification = unpaid

rawInterventionPaysBetaMaximality : PaymentStatus
rawInterventionPaysBetaMaximality = unpaid

runtimeProducerPaysGrokkingMechanism : PaymentStatus
runtimeProducerPaysGrokkingMechanism = unpaid
