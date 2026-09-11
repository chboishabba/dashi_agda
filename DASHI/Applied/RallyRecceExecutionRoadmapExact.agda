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
-- Status/navigation only.  Formal contracts, runnable producers, fixtures,
-- scientific validation and transfer receipts remain distinct currencies.
------------------------------------------------------------------------

data RoadmapStage : Set where
  paceNoteSemanticCarrier : RoadmapStage
  temporalStageStationFibre : RoadmapStage
  telemetryCanonicalAbi : RoadmapStage
  canonicalNormalizerRuntime : RoadmapStage
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
  executableFixturePresent : RoadmapStatus
  executableProducerMissing : RoadmapStatus
  validationFixtureMissing : RoadmapStatus
  empiricalReceiptMissing : RoadmapStatus
  deferredTransfer : RoadmapStatus

status : RoadmapStage → RoadmapStatus
status paceNoteSemanticCarrier = formalContractPresent
status temporalStageStationFibre = formalContractPresent
status telemetryCanonicalAbi = formalContractPresent
status canonicalNormalizerRuntime = executableFixturePresent
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
-- Typed execution dependencies, not topical adjacency.
------------------------------------------------------------------------

data DependsOn : RoadmapStage → RoadmapStage → Set where
  normalizerDependsOnAbi : DependsOn canonicalNormalizerRuntime telemetryCanonicalAbi
  syncDependsOnAbi : DependsOn sourceClockSynchronisation telemetryCanonicalAbi
  adapterDependsOnAbi : DependsOn simHubOrNativeAdapter telemetryCanonicalAbi
  adapterDependsOnNormalizer : DependsOn simHubOrNativeAdapter canonicalNormalizerRuntime
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
-- Shortest path from current frontier.
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
    "connect one real SimHub or game-native source to scripts/rally_telemetry_normalize.py"
    "every emitted sample retains source field, source clock/frame, canonical signal, representation/unit transform and provenance"
    true refl

secondExecutableTarget : NextExecutionTarget
secondExecutableTarget =
  next-execution-target
    traversalRecorder
    "persist synchronized canonical observations for one complete recce traversal"
    "replay preserves ordered observations plus traversal/station/source provenance; synchronization uncertainty remains explicit"
    true refl

firstScientificValidationTarget : NextExecutionTarget
firstScientificValidationTarget =
  next-execution-target
    beamNGHeldOutTruthFixture
    "estimate geometry/vehicle response without privileged truth, then compare against held-out simulator truth"
    "privileged truth is consumed only by validation comparison and never by deployable estimator input"
    true refl

------------------------------------------------------------------------
-- Runtime receipt for the bounded synthetic ABI fixture.
------------------------------------------------------------------------

record CanonicalNormalizerFixtureReceipt : Set where
  constructor canonical-normalizer-fixture-receipt
  field
    producerReference : String
    fixtureReference : String
    checkerReference : String
    sourceProvenanceRequired : Bool
    sourceProvenanceRequiredIsTrue : sourceProvenanceRequired ≡ true
    clockLineageRequired : Bool
    clockLineageRequiredIsTrue : clockLineageRequired ≡ true
    claimsLiveSimulatorIngestion : Bool
    claimsLiveSimulatorIngestionIsFalse : claimsLiveSimulatorIngestion ≡ false
    claimsScientificValidation : Bool
    claimsScientificValidationIsFalse : claimsScientificValidation ≡ false

canonicalNormalizerFixtureReceipt : CanonicalNormalizerFixtureReceipt
canonicalNormalizerFixtureReceipt =
  canonical-normalizer-fixture-receipt
    "scripts/rally_telemetry_normalize.py"
    "scripts/data/rally_recce/telemetry_normalisation_fixture.jsonl"
    "scripts/check_rally_telemetry_normalisation.py"
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Milestone firewalls.
------------------------------------------------------------------------

data FormalContractImpliesExecutableProducerPermission : Set where
data SyntheticFixtureImpliesLiveAdapterPermission : Set where
data BeamNGValidationImpliesRealWorldValidityPermission : Set where
data GeometryValidationImpliesTrajectoryOptimalityPermission : Set where
data OneConsumerValidationImpliesEveryConsumerPermission : Set where

formalContractDoesNotManufactureProducer :
  FormalContractImpliesExecutableProducerPermission → ⊥
formalContractDoesNotManufactureProducer ()

syntheticFixtureDoesNotManufactureLiveAdapter :
  SyntheticFixtureImpliesLiveAdapterPermission → ⊥
syntheticFixtureDoesNotManufactureLiveAdapter ()

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
    boundedCanonicalNormalizerPaid : Bool
    boundedCanonicalNormalizerPaidIsTrue : boundedCanonicalNormalizerPaid ≡ true
    liveSimulatorIngestionPaid : Bool
    liveSimulatorIngestionPaidIsFalse : liveSimulatorIngestionPaid ≡ false
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
    true refl
    false refl
    false refl
    false refl
    false refl
