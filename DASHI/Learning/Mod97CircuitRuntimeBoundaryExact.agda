module DASHI.Learning.Mod97CircuitRuntimeBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Runtime implementation, execution, historical identity, leakage, and
-- scientific payment are deliberately different carriers.
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
    requirementEdgePayment : PaymentStatus
    relationClassificationPayment : PaymentStatus
    betaMaximalityPayment : PaymentStatus
    mechanismPayment : PaymentStatus
open Mod97CircuitRuntimeFrontier public

------------------------------------------------------------------------
-- Current exact frontier on PR #900.
--
-- The checked-in Python producers implement a new-run checkpoint path and a
-- training-selected / held-out-evaluated raw intervention path. No numerical
-- run receipt has yet been observed here, and the historical receipt does not
-- pay exact original architecture/split identity.
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
    unpaid
    unpaid
    unpaid
    unpaid

------------------------------------------------------------------------
-- Explicit non-promotion witnesses.
------------------------------------------------------------------------

producerImplementationPaysExecution : PaymentStatus
producerImplementationPaysExecution = unpaid

rawInterventionPaysRequirementEdges : PaymentStatus
rawInterventionPaysRequirementEdges = unpaid

rawInterventionPaysRelationClassification : PaymentStatus
rawInterventionPaysRelationClassification = unpaid

rawInterventionPaysBetaMaximality : PaymentStatus
rawInterventionPaysBetaMaximality = unpaid

runtimeProducerPaysGrokkingMechanism : PaymentStatus
runtimeProducerPaysGrokkingMechanism = unpaid
