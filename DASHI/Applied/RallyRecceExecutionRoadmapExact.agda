module DASHI.Applied.RallyRecceExecutionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Applied.RallyReccePaceNoteFibreOverTimeExact as Rally
import DASHI.Applied.RallyTelemetryObservationNormalisationExact as Telemetry
import DASHI.Core.ConsumerIndexedModelFibreExact as ModelFibre

------------------------------------------------------------------------
-- EXECUTION ROADMAP
--
-- This is a status/navigation owner.  It does not promote a formal contract
-- into a runnable producer, fixture result or validation receipt.
------------------------------------------------------------------------

data RoadmapStage : Set where
  paceNoteSemanticCarrier : RoadmapStage
  temporalStageStationFibre : RoadmapStage
  telemetryCanonicalAbi : RoadmapStage
  sourceClockSynchronisation : RoadmapStage
  simHubOrNativeAdapter : RoadmapStage
  traversalRecorder : RoadmapStage
  renderedVideoAlignment : RoadmapStage
  crossRunRegistration : RoadmapStage
  roadGeometryEstimator : RoadmapStage
  effectiveVehicleEstimator : RoadmapStage
  beamNGHeldOutTruthFixture : RoadmapStage
  consumerIndexedTrajectorySolver : RoadmapStage
  dirtWrcBlackBoxTransfer : RoadmapStage
  realVehicleTransfer : RoadmapStage

data RoadmapStatus : Set where
  formalContractPresent : RoadmapStatus
  executableProducerMissing : RoadmapStatus
  validationFixtureMissing : RoadmapStatus
  empiricalReceiptMissing : RoadmapStatus
  deferredTransfer : RoadmapStatus

status : RoadmapStage → RoadmapStatus
status paceNoteSemanticCarrier = formalContractPresent
status temporalStageStationFibre = formalContractPresent
status telemetryCanonicalAbi = formalContractPresent
status sourceClockSynchronisation = formalContractPresent
status simHubOrNativeAdapter = executableProducerMissing
status traversalRecorder = executableProducerMissing
status renderedVideoAlignment = executableProducerMissing
status crossRunRegistration = executableProducerMissing
status roadGeometryEstimator = executableProducerMissing
status effectiveVehicleEstimator = executableProducerMissing
status beamNGHeldOutTruthFixture = validationFixtureMissing
status consumerIndexedTrajectorySolver = executableProducerMissing
status dirtWrcBlackBoxTransfer = empiricalReceiptMissing
status realVehicleTransfer = deferredTransfer

------------------------------------------------------------------------
-- Typed dependency edges.  These are execution-order obligations, not merely
-- topical adjacency.
------------------------------------------------------------------------

data DependsOn : RoadmapStage → RoadmapStage → Set where
  syncDependsOnAbi : DependsOn sourceClockSynchronisation telemetryCanonicalAbi
  adapterDependsOnAbi : DependsOn simHubOrNativeAdapter telemetryCanonicalAbi
  recorderDependsOnAdapter : DependsOn traversalRecorder simHubOrNativeAdapter
  recorderDependsOnSync : DependsOn traversalRecorder sourceClockSynchronisation
  videoDependsOnRecorder : DependsOn renderedVideoAlignment traversalRecorder
  registrationDependsOnRecorder : DependsOn crossRunRegistration traversalRecorder
  geometryDependsOnVideo : DependsOn roadGeometryEstimator renderedVideoAlignment
  geometryDependsOnRegistration : DependsOn roadGeometryEstimator crossRunRegistration
  geometryDependsOnPaceNotes : DependsOn roadGeometryEstimator paceNoteSemanticCarrier
  vehicleDependsOnRecorder : DependsOn effectiveVehicleEstimator traversalRecorder
  vehicleDependsOnRegistration : DependsOn effectiveVehicleEstimator crossRunRegistration
  beamNGDependsOnGeometry : DependsOn beamNGHeldOutTruthFixture roadGeometryEstimator
  beamNGDependsOnVehicle : DependsOn beamNGHeldOutTruthFixture effectiveVehicleEstimator
  solverDependsOnGeometry : DependsOn consumerIndexedTrajectorySolver roadGeometryEstimator
  solverDependsOnVehicle : DependsOn consumerIndexedTrajectorySolver effectiveVehicleEstimator
  solverDependsOnFibre : DependsOn consumerIndexedTrajectorySolver temporalStageStationFibre
  blackBoxDependsOnBeamNG : DependsOn dirtWrcBlackBoxTransfer beamNGHeldOutTruthFixture
  blackBoxDependsOnSolver : DependsOn dirtWrcBlackBoxTransfer consumerIndexedTrajectorySolver
  realDependsOnBlackBox : DependsOn realVehicleTransfer dirtWrcBlackBoxTransfer

------------------------------------------------------------------------
-- Shortest implementation path from the current formal frontier.
------------------------------------------------------------------------

record NextExecutionTarget : Set where
  constructor next-execution-target
  field
    stage : RoadmapStage
    targetReference : String
    acceptanceReference : String
    doesNotClaimTargetAlreadyImplemented : Bool
    doesNotClaimTargetAlreadyImplementedIsTrue :
      doesNotClaimTargetAlreadyImplemented ≡ true

firstExecutableTarget : NextExecutionTarget
firstExecutableTarget =
  next-execution-target
    simHubOrNativeAdapter
    "implement one real telemetry adapter into RallyTelemetryObservationNormalisationExact"
    "record source field, source clock/frame, canonical signal, unit/representation transform and provenance for every emitted sample"
    true refl

secondExecutableTarget : NextExecutionTarget
secondExecutableTarget =
  next-execution-target
    traversalRecorder
    "persist synchronized canonical observations for one complete recce traversal"
    "replay yields the same ordered canonical observation references and preserves traversal/station/source provenance"
    true refl

firstScientificValidationTarget : NextExecutionTarget
firstScientificValidationTarget =
  next-execution-target
    beamNGHeldOutTruthFixture
    "estimate geometry/vehicle response without privileged truth, then compare against held-out simulator truth"
    "privileged truth is consumed only by validation comparison and never by the deployable estimator input"
    true refl

------------------------------------------------------------------------
-- Milestone firewalls.
------------------------------------------------------------------------

data FormalContractImpliesExecutableProducerPermission : Set where
data BeamNGValidationImpliesRealWorldValidityPermission : Set where
data GeometryValidationImpliesTrajectoryOptimalityPermission : Set where

data OneConsumerValidationImpliesEveryConsumerPermission : Set where

formalContractDoesNotManufactureProducer :
  FormalContractImpliesExecutableProducerPermission → ⊥
formalContractDoesNotManufactureProducer ()

beamNGValidationDoesNotAutoTransferToReality :
  BeamNGValidationImpliesRealWorldValidityPermission → ⊥
beamNGValidationDoesNotAutoTransferToReality ()

geometryValidationDoesNotProveTrajectoryOptimality :
  GeometryValidationImpliesTrajectoryOptimalityPermission → ⊥
geometryValidationDoesNotProveTrajectoryOptimality ()

oneConsumerValidationDoesNotTransferUniversally :
  OneConsumerValidationImpliesEveryConsumerPermission → ⊥
oneConsumerValidationDoesNotTransferUniversally ()

------------------------------------------------------------------------
-- Existing boundaries remain authoritative.
------------------------------------------------------------------------

rallyBoundary : Rally.RallyRecceBoundary
rallyBoundary = Rally.canonicalRallyRecceBoundary

telemetryBoundary : Telemetry.RallyTelemetryNormalisationBoundary
telemetryBoundary = Telemetry.canonicalRallyTelemetryNormalisationBoundary

modelBoundary : ModelFibre.ConsumerIndexedModelBoundary
modelBoundary = ModelFibre.canonicalConsumerIndexedModelBoundary

record RallyRecceRoadmapBoundary : Set where
  constructor rally-recce-roadmap-boundary
  field
    formalOntologyPaid : Bool
    formalOntologyPaidIsTrue : formalOntologyPaid ≡ true
    executableIngestionPaid : Bool
    executableIngestionPaidIsFalse : executableIngestionPaid ≡ false
    heldOutSimulatorValidationPaid : Bool
    heldOutSimulatorValidationPaidIsFalse : heldOutSimulatorValidationPaid ≡ false
    trajectorySolverPaid : Bool
    trajectorySolverPaidIsFalse : trajectorySolverPaid ≡ false
    realWorldTransferPaid : Bool
    realWorldTransferPaidIsFalse : realWorldTransferPaid ≡ false

canonicalRallyRecceRoadmapBoundary : RallyRecceRoadmapBoundary
canonicalRallyRecceRoadmapBoundary =
  rally-recce-roadmap-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
