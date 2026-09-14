module DASHI.Learning.Mod97CircuitRuntimeBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Runtime implementation, execution, historical identity, leakage,
-- observation adequacy, and scientific payment are deliberately different
-- carriers.
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

data ClassificationPolicyStatus : Set where
  notFrozenBeforeHeldOutEvaluation : ClassificationPolicyStatus
  frozenBeforeHeldOutEvaluation : ClassificationPolicyStatus

data RequirementDirectionStatus : Set where
  unavailableFromCurrentObservation : RequirementDirectionStatus
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
    relationClassifierProducer : ProducerStatus
    relationClassifierExecution : ExecutionStatus
    relationGraphCompilerProducer : ProducerStatus
    relationGraphCompilerExecution : ExecutionStatus
    betaProducer : ProducerStatus
    betaExecution : ExecutionStatus
    historicalRunIdentity : IdentityStatus
    historicalConfigurationIdentity : IdentityStatus
    selectionLeakage : SelectionLeakageStatus
    classificationPolicyStatus : ClassificationPolicyStatus
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
-- The checked-in Python surfaces now implement:
--   checkpoint regeneration under explicit new-run provenance,
--   leakage-safe singleton/joint interventions,
--   producer-safe conflict/independent classification for the current
--     symmetric observation,
--   fail-closed compilation of already-paid canonical relation receipts, and
--   exact finite closed-compatible-capacity enumeration.
--
-- Candidate selection and relation-classification policy are separate leakage
-- coordinates. The candidate rule is fixed on the training carrier; the
-- interaction threshold plus adequacy/power policy must likewise be frozen
-- before held-out evaluation. Implementation is not execution.
--
-- Raw signed held-out loss changes are retained, while an orientation-aware
-- adapter maps only positive loss increase into non-negative micro-loss Nat
-- damage. The current classifier can pay only conflict/independent once its
-- frozen-policy and adequacy/power gates are supplied. It cannot manufacture a
-- gluingRequirement edge.
--
-- Canonical gluingRequirement is a directed selection-closure relation: if one
-- candidate is selected, another may also need to be selected to close an
-- operator/seam compatibility condition. It is not defined as a physical
-- hidden-unit causal edge. The current singleton/joint pair-ablation observation
-- is symmetric with respect to opposite requirement directions, so it cannot
-- pay which directed closure relation holds. A richer externally paid
-- observation/consumer receipt is needed before requirement direction can be
-- promoted.
--
-- The graph compiler rejects unpaid relation classifications and rejects
-- gluingRequirement without a paid direction. The beta producer can exhaust a
-- supplied paid finite relation graph, but no empirical relation graph has yet
-- been executed through this chain here. Therefore relation classification and
-- beta maximality remain unpaid at the empirical checkpoint layer.
------------------------------------------------------------------------

currentMod97RuntimeFrontier : Mod97CircuitRuntimeFrontier
currentMod97RuntimeFrontier =
  mod97CircuitRuntimeFrontier
    implemented
    notExecuted
    implemented
    notExecuted
    implemented
    notExecuted
    implemented
    notExecuted
    implemented
    notExecuted
    notEstablished
    notEstablished
    heldOutNotUsedForSelection
    frozenBeforeHeldOutEvaluation
    paid
    unavailableFromCurrentObservation
    unpaid
    unpaid
    unpaid
    unpaid

------------------------------------------------------------------------
-- Explicit non-promotion witnesses.
------------------------------------------------------------------------

producerImplementationPaysExecution : PaymentStatus
producerImplementationPaysExecution = unpaid

relationClassifierImplementationPaysRelationClassification : PaymentStatus
relationClassifierImplementationPaysRelationClassification = unpaid

relationGraphCompilerImplementationPaysRelationGraph : PaymentStatus
relationGraphCompilerImplementationPaysRelationGraph = unpaid

betaProducerImplementationPaysBetaMaximality : PaymentStatus
betaProducerImplementationPaysBetaMaximality = unpaid

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
