module DASHI.Geometry.SeaMeInItGovernedPipeline where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Governance.GovernedArtifactCore

------------------------------------------------------------------------
-- Concrete carriers used by the SeaMeInIt body-to-pattern pipeline.


data Hash : Set where
  sha256 : Nat → Hash

data BodyState : Set where
  rawImageFit refinedCandidate repairedExport : BodyState

data CanonicalSource : Set where
  rawImageSource refinedCandidateSource : CanonicalSource

data GateWarning : Set where
  lowViewDiversity
  longLensFlatteningRisk
  coarseDetectorEvidence
  finalExportRepaired
  retainedDiagnosticWarning : GateWarning

data GateBlocker : Set where
  nonFiniteCandidate
  malformedPolicy
  solverFailure
  excessiveBetaShift
  residualDegradation
  invalidFinalTopology
  lowBodyTrust
  skullResidualExceeded
  missingLineage : GateBlocker

data Consumer : Set where
  undersuit hardShell panelTransfer patternExport manufacturingExport : Consumer

------------------------------------------------------------------------
-- Synchronized calibrated multi-view observations strengthen evidence but do
-- not bypass the authority boundary.

record CameraModel : Set where
  constructor cameraModel
  field
    intrinsicHash : Hash
    extrinsicHash : Hash

open CameraModel public

record MultiViewObservation : Set where
  constructor multiViewObservation
  field
    frameHash       : Hash
    cameras         : List CameraModel
    synchronized    : Bool
    calibrated      : Bool
    observationHash : Hash

open MultiViewObservation public

record JointImageCandidate : Set where
  constructor jointImageCandidate
  field
    observation      : MultiViewObservation
    imageBetaHash    : Hash
    reprojectionHash : Hash
    candidateBody    : BodyState

open JointImageCandidate public

multiViewCalibrationIsEvidenceNotAuthority : Bool
multiViewCalibrationIsEvidenceNotAuthority = true

------------------------------------------------------------------------
-- Gate 0: effective policy and bounded image-anchored refinement.

record RefinementPolicy : Set where
  constructor refinementPolicy
  field
    measurementModelHash : Hash
    measurementOrderHash : Hash
    scaleRuleHash         : Hash
    betaBoundsHash        : Hash
    priorWeight           : Nat
    anchorWeight          : Nat
    residualThreshold     : Nat
    betaShiftThreshold    : Nat
    solverIdentityHash    : Hash
    solverTolerance       : Nat
    solverIterationLimit  : Nat
    effectivePolicyHash   : Hash

open RefinementPolicy public

record RefinementEvidence : Set where
  constructor refinementEvidence
  field
    anchorBetaHash      : Hash
    candidateBetaHash   : Hash
    anchorResidual      : Nat
    candidateResidual   : Nat
    residualDelta       : Nat
    betaShift           : Nat
    priorCost           : Nat
    anchorCost          : Nat
    activeBoundCount    : Nat
    boundedOutputFinite : Bool
    topologyFinite      : Bool

open RefinementEvidence public

RefinementReceipt : Set
RefinementReceipt =
  Receipt BodyState RefinementPolicy RefinementEvidence Hash GateWarning GateBlocker

canonicalSourceFor : Decision → CanonicalSource
canonicalSourceFor promote = refinedCandidateSource
canonicalSourceFor abstain = rawImageSource
canonicalSourceFor reject  = rawImageSource

selectedPreRepairFor : Decision → BodyState
selectedPreRepairFor promote = refinedCandidate
selectedPreRepairFor abstain = rawImageFit
selectedPreRepairFor reject  = rawImageFit

abstainedRefinementKeepsRaw : selectedPreRepairFor abstain ≡ rawImageFit
abstainedRefinementKeepsRaw = refl

rejectedRefinementKeepsRaw : selectedPreRepairFor reject ≡ rawImageFit
rejectedRefinementKeepsRaw = refl

promotedRefinementSelectsCandidate :
  selectedPreRepairFor promote ≡ refinedCandidate
promotedRefinementSelectsCandidate = refl

------------------------------------------------------------------------
-- The final export has an independent body decision.

record TopologyEvidence : Set where
  constructor topologyEvidence
  field
    vertexCount       : Nat
    faceCount         : Nat
    finiteCoordinates : Bool
    legalFaceIndices  : Bool
    closedEdges       : Bool
    connectedSurface  : Bool

open TopologyEvidence public

record FinalExportEvidence : Set where
  constructor finalExportEvidence
  field
    topology              : TopologyEvidence
    skullResidual         : Nat
    landmarkResidual      : Nat
    repairRmsDisplacement : Nat
    repairMaxDisplacement : Nat
    bodyFitConfidence     : Nat

open FinalExportEvidence public

record BodyCarrierReceiptV2 : Set where
  constructor bodyCarrierReceiptV2
  field
    sourceHash                : Hash
    refinementReceiptHash     : Hash
    refinementDecision        : Decision
    rawReprojectionHash       : Hash
    refinedPreRepairHash      : Hash
    selectedPreRepairHash     : Hash
    repairedExportHash        : Hash
    canonicalSource           : CanonicalSource
    canonicalSourceCorrect    :
      canonicalSource ≡ canonicalSourceFor refinementDecision
    selectedCheckpoint        : BodyState
    selectedCheckpointCorrect :
      selectedCheckpoint ≡ selectedPreRepairFor refinementDecision
    rawTopology               : TopologyEvidence
    refinedPreRepairTopology  : TopologyEvidence
    finalExportEvidence       : FinalExportEvidence
    diagnosticSeverity        : DiagnosticSeverity
    retainedWarnings          : List GateWarning
    bodyBlockers              : List GateBlocker
    bodyDecision              : Decision
    blockedConsumers          : List Consumer
    bodyCarrierReceiptHash    : Hash

open BodyCarrierReceiptV2 public

record IndependentGate0Decisions : Set where
  constructor independentGate0Decisions
  field
    localRefinementDecision : Decision
    finalBodyDecision       : Decision

open IndependentGate0Decisions public

rawPromotesAfterRefinementAbstains : IndependentGate0Decisions
rawPromotesAfterRefinementAbstains = independentGate0Decisions abstain promote

coarseBodyAbstainsAfterRefinementAbstains : IndependentGate0Decisions
coarseBodyAbstainsAfterRefinementAbstains =
  independentGate0Decisions abstain abstain

warningsDoNotUniversallyVetoBody : WarningCompatiblePromotion GateWarning
warningsDoNotUniversallyVetoBody =
  warningCompatiblePromotion retainedDiagnosticWarning refl

------------------------------------------------------------------------
-- Gate 1--5 receipt-DAG stages.


data PipelineStage : Set where
  observationStage
  imageFitStage
  refinementStage
  bodyCarrierStage
  bodyFieldStage
  seamCostStage
  solverPromotionStage
  cutTopologyStage
  metricCorrectionStage
  sequentialSearchStage
  serializationCompetitionStage
  panelUnwrapStage
  manufacturingArtifactStage : PipelineStage

record StageArtifact : Set where
  constructor stageArtifact
  field
    stage             : PipelineStage
    stageArtifactHash : Hash
    stageReceiptHash  : Hash

open StageArtifact public

record StageEdge : Set where
  constructor stageEdge
  field
    parent                    : StageArtifact
    child                     : StageArtifact
    parentReceiptHash         : Hash
    childConsumesParentReceipt :
      stageReceiptHash parent ≡ parentReceiptHash

open StageEdge public

------------------------------------------------------------------------
-- Gate 6 v1 claim boundary.

record DiagnosticDeltaComposition : Set where
  constructor diagnosticDeltaComposition
  field
    originalMetricHash      : Hash
    firstOperatorDeltaHash  : Hash
    secondOperatorDeltaHash : Hash
    sequentiallyMaterialized : Bool
    orderedSearch            : Bool
    sameFamilyRepetition     : Bool

open DiagnosticDeltaComposition public

gate6V1IsSequential : Bool
gate6V1IsSequential = false

gate6V1ProvesBasisExhaustion : Bool
gate6V1ProvesBasisExhaustion = false

------------------------------------------------------------------------
-- Gate 6 v2: ordered materialized transitions with recomputation.


data PanelOperator : Set where
  stretchZone
  gussetPatch
  dartWedge
  lensPatch
  reliefPath
  reliefTree
  drainPath
  grainRotation
  easeBand
  seamRelocation
  boundarySplit
  variableKnitProxy : PanelOperator

record PanelState : Set where
  constructor panelState
  field
    geometryHash      : Hash
    topologyHash      : Hash
    seamHash          : Hash
    uvHash            : Hash
    residualFieldHash : Hash
    backendMetricHash : Hash

open PanelState public

record PanelEvidence : Set where
  constructor panelEvidence
  field
    faceConservation             : Bool
    topologyValid                : Bool
    geometryFinite               : Bool
    backendRerun                 : Bool
    residualsRecomputed          : Bool
    admissibleOperatorsRecomputed : Bool
    foldoverCount                : Nat
    worstDistortion              : Nat
    chartCount                   : Nat

open PanelEvidence public

PanelTransition : Set
PanelTransition = SearchTransition PanelState PanelOperator PanelEvidence Hash

record OrderedMaterializedPair : Set where
  constructor orderedMaterializedPair
  field
    firstTransition  : PanelTransition
    secondTransition : PanelTransition
    secondConsumesFirstChild :
      parentStateHash secondTransition ≡ childStateHash firstTransition
    firstActuallyMaterialized  : Bool
    secondActuallyMaterialized : Bool

open OrderedMaterializedPair public

record Gate6SearchReceiptV2 : Set₁ where
  constructor gate6SearchReceiptV2
  field
    searchPolicy      : BoundedSearchPolicy Hash
    initialPanelState : PanelState
    transitions       : List PanelTransition
    boundedConclusion : BoundedNoPromotion Hash searchPolicy
    gate6ReceiptHash  : Hash

open Gate6SearchReceiptV2 public

------------------------------------------------------------------------
-- Failure diagnosis before serializer replacement.


data FailureClass : Set where
  operatorExpressivityFailure
  serializationBackendFailure
  panelizationFailure
  physicalOrMaterialPolicyInfeasibility
  indeterminateFailure : FailureClass

record FailureDiagnosis : Set where
  constructor failureDiagnosis
  field
    classifications      : List FailureClass
    evidenceHash         : Hash
    diagnosisReceiptHash : Hash

open FailureDiagnosis public

record BT369SerializerIndication : Set where
  constructor bt369SerializerIndication
  field
    validGarmentGeometryExists : Bool
    currentSerializationFails  : Bool
    operatorBasisAdequate      : Bool
    panelizationAdequate       : Bool
    physicalPolicyFeasible     : Bool

open BT369SerializerIndication public

automaticBT369Promotion : Bool
automaticBT369Promotion = false

------------------------------------------------------------------------
-- Explicit global claim boundaries.

trueBodyReconstructionPromoted : Bool
trueBodyReconstructionPromoted = false

continuumGarmentOptimalityPromoted : Bool
continuumGarmentOptimalityPromoted = false

automaticManufacturingAuthorityPromoted : Bool
automaticManufacturingAuthorityPromoted = false
