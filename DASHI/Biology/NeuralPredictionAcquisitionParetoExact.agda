module DASHI.Biology.NeuralPredictionAcquisitionParetoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.NeuralPredictionDirectionExact as Direction
import DASHI.Biology.GABANeuroAIContextParetoSnowballExact as Pareto0
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- ROUND-2 PARETO / ACQUISITION SNOWBALL FOR NEURAL PREDICTION
------------------------------------------------------------------------

data PredictionAcquisitionStatus : Set where
  acquiredBounded : PredictionAcquisitionStatus
  acquiredMechanismBoundary : PredictionAcquisitionStatus
  independentReplicationRequired : PredictionAcquisitionStatus
  benchmarkExpansionRequired : PredictionAcquisitionStatus
  crossModalValidationRequired : PredictionAcquisitionStatus

data PredictionAcquisitionAxis : Set where
  directionAxis : PredictionAcquisitionAxis
  provenanceAxis : PredictionAcquisitionAxis
  modalityAxis : PredictionAcquisitionAxis
  subjectTransferAxis : PredictionAcquisitionAxis
  stimulusTransferAxis : PredictionAcquisitionAxis
  populationOutcomeAxis : PredictionAcquisitionAxis
  mechanismIdentityAxis : PredictionAcquisitionAxis
  calibrationBurdenAxis : PredictionAcquisitionAxis

record PredictionAcquisitionNode : Set where
  constructor prediction-acquisition-node
  field
    label : String
    status : PredictionAcquisitionStatus
    discoveryRoute : Snowball.DiscoveryRoute
    axis : PredictionAcquisitionAxis
    currentReceiptReference : String
    nextEvidenceShape : String
    authorityBoundary : String

open PredictionAcquisitionNode public

metaMechanismSeparationAcquisition : PredictionAcquisitionNode
metaMechanismSeparationAcquisition =
  prediction-acquisition-node
    "brain-model representation / learning-mechanism separation"
    acquiredMechanismBoundary
    Snowball.externalKnowledgeComparison
    mechanismIdentityAxis
    "Meta brain-model convergence 2025 + backprop-gradient misalignment 2026 receipts"
    "Replicate across architectures, sensory domains and recording modalities while preserving representational-similarity != learning-mechanism identity."
    "Meta-authored model/brain comparison; no biological implementation authority."

videoNeuroforecastAcquisition : PredictionAcquisitionNode
videoNeuroforecastAcquisition =
  prediction-acquisition-node
    "dynamic commercial-video neuroforecasting"
    acquiredBounded
    Snowball.externalKnowledgeComparison
    stimulusTransferAxis
    "Motoki et al. 2020 video-advertising fMRI/social-sharing receipt"
    "Cross-platform held-out video sets with frozen feature/ROI definition and independently logged sharing outcomes; compare neural-only, self-report-only, and joint models."
    "Forecasting remains stimulus/platform/sample/outcome scoped."

neuralinkIndependentReplicationAcquisition : PredictionAcquisitionNode
neuralinkIndependentReplicationAcquisition =
  prediction-acquisition-node
    "Neuralink calibration-burden independent replication"
    independentReplicationRequired
    Snowball.experimentalDesign
    calibrationBurdenAxis
    "Primary Neuralink >50k-hour/weeks-without-recalibration source plus secondary exact-burden report"
    "Independent per-participant calibration-time distribution, decoder-drift survival curve, task-normalized throughput, and adverse/missing-session accounting."
    "Company result remains company result until independent clinical/academic replication."

crossParticipantBCIAcquisition : PredictionAcquisitionNode
crossParticipantBCIAcquisition =
  prediction-acquisition-node
    "held-out-participant BCI transfer"
    independentReplicationRequired
    Snowball.experimentalDesign
    subjectTransferAxis
    "Cross-participant superiority currently unpaid in acquired Neuralink evidence"
    "Frozen encoder/decoder evaluated on held-out participants with matched calibration budget, same task definition, longitudinal drift endpoint and explicit failure distribution."
    "Within-participant success cannot promote to cross-participant decoder universality."

metaNeuralBenchExpansionAcquisition : PredictionAcquisitionNode
metaNeuralBenchExpansionAcquisition =
  prediction-acquisition-node
    "NeuralBench multimodal benchmark expansion"
    benchmarkExpansionRequired
    Snowball.externalKnowledgeComparison
    modalityAxis
    "Meta NeuralBench EEG v1.0: 36 tasks, 14 architectures, 94 datasets; preliminary MEG/fMRI extensions"
    "Common frozen benchmark slices for EEG, MEG, fMRI and spike-model families with modality-specific preprocessing and non-collapsed endpoint semantics."
    "Unified benchmark infrastructure does not make modalities equivalent."

------------------------------------------------------------------------
-- Multimodal interface cross-pollination: NeuralSet and Neuralink datarepo.
------------------------------------------------------------------------

neuralinkDatarepoSource : Source.AttributedSource
neuralinkDatarepoSource =
  Source.mkNoDOISource
    "Neuralink"
    "datarepo - Neuralink's platform for complex data"
    "Neuralink Updates"
    "2025"
    "https://neuralink.com/updates/datarepo/"
    Source.institutionalSource
    "Pays a company-described uniform data-catalog/query interface over heterogeneous operational and scientific data including real-time neural signals, histopathology, surgery video/telemetry and 3D brain scans. The interface is software/data infrastructure, not evidence that modalities measure the same latent variable."
    Source.publicAttribution

record MultimodalInterfaceBoundary : Set where
  constructor multimodal-interface-boundary
  field
    metaNeuralSetReference : String
    neuralinkDatarepoSource : Source.AttributedSource
    commonInterfaceEnablesJointQuery : Bool
    commonInterfaceEnablesJointQueryIsTrue : commonInterfaceEnablesJointQuery ≡ true
    commonInterfaceImpliesMeasurementIdentity : Bool
    commonInterfaceImpliesMeasurementIdentityIsFalse :
      commonInterfaceImpliesMeasurementIdentity ≡ false
    crossModalJoinImpliesCausalBridge : Bool
    crossModalJoinImpliesCausalBridgeIsFalse : crossModalJoinImpliesCausalBridge ≡ false
    provenanceMustSurviveJoin : Bool
    provenanceMustSurviveJoinIsTrue : provenanceMustSurviveJoin ≡ true
    assayAndModalitySemanticsRemainTyped : Bool
    assayAndModalitySemanticsRemainTypedIsTrue : assayAndModalitySemanticsRemainTyped ≡ true

canonicalMultimodalInterfaceBoundary : MultimodalInterfaceBoundary
canonicalMultimodalInterfaceBoundary =
  multimodal-interface-boundary
    "Meta NeuralSet 2026: unified scalable interface for fMRI, M/EEG, spikes and naturalistic stimuli"
    neuralinkDatarepoSource
    true refl false refl false refl true refl true refl

multimodalInterfaceAcquisition : PredictionAcquisitionNode
multimodalInterfaceAcquisition =
  prediction-acquisition-node
    "multimodal neural data interface with typed measurement semantics"
    crossModalValidationRequired
    Snowball.externalKnowledgeComparison
    modalityAxis
    "Meta NeuralSet + Neuralink datarepo infrastructure sources"
    "Define join receipts that preserve per-modality acquisition protocol, assay semantics, clock/alignment, participant identity boundary and source provenance across shared query surfaces."
    "Software interoperability is not measurement equivalence, causal identification, or clinical authority."

canonicalPredictionAcquisitionFrontier : List PredictionAcquisitionNode
canonicalPredictionAcquisitionFrontier =
  metaMechanismSeparationAcquisition ∷
  videoNeuroforecastAcquisition ∷
  neuralinkIndependentReplicationAcquisition ∷
  crossParticipantBCIAcquisition ∷
  metaNeuralBenchExpansionAcquisition ∷
  multimodalInterfaceAcquisition ∷ []

record NeuralPredictionAcquisitionBoundary : Set where
  constructor neural-prediction-acquisition-boundary
  field
    inheritedParetoBoundary : Pareto0.GABANeuroAIParetoSnowballBoundary
    frontier : List PredictionAcquisitionNode
    directionRemainsExplicit : Bool
    directionRemainsExplicitIsTrue : directionRemainsExplicit ≡ true
    provenanceRemainsExplicit : Bool
    provenanceRemainsExplicitIsTrue : provenanceRemainsExplicit ≡ true
    softwareUnificationDoesNotCollapseMeasurementTypes : Bool
    softwareUnificationDoesNotCollapseMeasurementTypesIsTrue :
      softwareUnificationDoesNotCollapseMeasurementTypes ≡ true
    mechanismIdentityRemainsSeparateFromPredictivity : Bool
    mechanismIdentityRemainsSeparateFromPredictivityIsTrue :
      mechanismIdentityRemainsSeparateFromPredictivity ≡ true
    independentReplicationIsSeparateAcquisitionAxis : Bool
    independentReplicationIsSeparateAcquisitionAxisIsTrue :
      independentReplicationIsSeparateAcquisitionAxis ≡ true

canonicalNeuralPredictionAcquisitionBoundary : NeuralPredictionAcquisitionBoundary
canonicalNeuralPredictionAcquisitionBoundary =
  neural-prediction-acquisition-boundary
    Pareto0.canonicalGABANeuroAIParetoSnowballBoundary
    canonicalPredictionAcquisitionFrontier
    true refl true refl true refl true refl true refl
