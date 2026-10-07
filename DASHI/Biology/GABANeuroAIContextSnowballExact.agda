module DASHI.Biology.GABANeuroAIContextSnowballExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.GABAPhenotypeEvidenceInstantiationExact as GABA
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Biology.AliceBrownThreadInquirySynthesisExact as Alice
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact as Levin

------------------------------------------------------------------------
-- GABA / NEURO-AI / CONTEXT SNOWBALL
--
-- This tranche snowballs the GABA evidence work into existing dyadic/observer,
-- fMRI/connectome proxy, experimental-design and multiscale bioelectric owners.
-- Attribution is claim-relative: Meta-authored NeuroAI work is not conflated
-- with independent neuroforecasting papers that happen to use social-media
-- outcomes, and Neuralink company updates are retained as company evidence.
------------------------------------------------------------------------

data NeuroAISourceRole : Set where
  metaAuthoredNeuroAI : NeuroAISourceRole
  independentNeuroforecasting : NeuroAISourceRole
  companyBCIUpdate : NeuroAISourceRole

data NeuralModality : Set where
  fMRI : NeuralModality
  fMRIMEG : NeuralModality
  EEGMEG : NeuralModality
  intracorticalSpikes : NeuralModality
  multimodalNeuralRecordings : NeuralModality

record NeuroAISourceReceipt : Set where
  constructor neuro-ai-source-receipt
  field
    source : Source.AttributedSource
    role : NeuroAISourceRole
    modality : NeuralModality
    paidClaim : String
    boundary : String

record NeuroforecastingSourceReceipt : Set where
  constructor neuroforecasting-source-receipt
  field
    source : Source.AttributedSource
    modality : NeuralModality
    populationOutcome : String
    paidClaim : String
    boundary : String

metaTRIBEv2Source : Source.AttributedSource
metaTRIBEv2Source =
  Source.mkNoDOISource
    "Meta FAIR"
    "Introducing TRIBE v2: A Predictive Foundation Model Trained to Understand How the Human Brain Processes Complex Stimuli"
    "AI at Meta"
    "2026"
    "https://ai.meta.com/blog/tribe-v2-brain-predictive-foundation-model"
    Source.institutionalSource
    "Pays Meta's report that TRIBE v2 predicts high-resolution fMRI responses to naturalistic sights, sounds and language across more than 700 healthy volunteers, including zero-shot prediction claims for new subjects, languages and tasks. It does not convert fMRI into direct thought identity or clinical authority."
    Source.publicAttribution

metaBrain2QwertySource : Source.AttributedSource
metaBrain2QwertySource =
  Source.mkNoDOISource
    "Meta FAIR"
    "From Brain Waves to Words: Brain2Qwerty Offers a New Path to Communication Without Surgery"
    "AI at Meta"
    "2026"
    "https://ai.meta.com/blog/brain2qwerty-brain-ai-human-communication/"
    Source.institutionalSource
    "Pays Meta's report of improved real-time sentence decoding from non-invasive neural recordings. Decoder performance does not imply unrestricted mind reading or latent-state identity."
    Source.publicAttribution

metaNeuralSetSource : Source.AttributedSource
metaNeuralSetSource =
  Source.mkNoDOISource
    "Jean Remi King et al.; Meta FAIR"
    "NeuralSet: A High-Performing Python Package for Neuro-AI"
    "AI at Meta Research"
    "2026"
    "https://ai.meta.com/research/publications/neuralset-a-high-performing-python-package-for-neuro-ai/"
    Source.institutionalSource
    "Pays a unified computational interface across fMRI, M/EEG, spikes and naturalistic stimuli with provenance-aware scalable data processing; it does not identify modalities or assays as interchangeable measurements."
    Source.publicAttribution

metaNeuralBenchSource : Source.AttributedSource
metaNeuralBenchSource =
  Source.mkNoDOISource
    "Hubert Banville et al.; Meta FAIR"
    "NeuralBench: A Unifying Framework to Benchmark NeuroAI Models"
    "AI at Meta Research"
    "2026"
    "https://ai.meta.com/research/publications/neuralbench-a-unifying-framework-to-benchmark-neuroai-models/"
    Source.institutionalSource
    "Pays a benchmark framework for NeuroAI models and reports that current foundation models only marginally outperform task-specific models across the initial EEG benchmark while many cognitive and clinical tasks remain challenging."
    Source.publicAttribution

metaBrainModelConvergenceSource : Source.AttributedSource
metaBrainModelConvergenceSource =
  Source.mkNoDOISource
    "Meta FAIR"
    "Disentangling the Factors of Convergence between Brains and Computer Vision Models"
    "AI at Meta Research"
    "2025"
    "https://ai.meta.com/research/publications/disentangling-the-factors-of-convergence-between-brains-and-computer-vision-models/"
    Source.institutionalSource
    "Pays comparison of self-supervised vision-model representations with human ultra-high-field fMRI and MEG using representational, topographical and temporal metrics. Representation similarity is not mechanistic identity."
    Source.publicAttribution

neuralink2026PretrainingSource : Source.AttributedSource
neuralink2026PretrainingSource =
  Source.mkNoDOISource
    "Neuralink"
    "Pretraining on 50,000 Hours of Unlabeled Brain Data"
    "Neuralink Updates"
    "2026"
    "https://neuralink.com/updates/"
    Source.institutionalSource
    "Company-reported October 2026 update: self-supervised pretraining on participant-specific unlabeled intracortical recordings reduced recalibration burden for some participants and improved decoder stability. This is company evidence, not independent replication or population-wide guarantee."
    Source.publicAttribution

scholz2017ViralitySource : Source.AttributedSource
scholz2017ViralitySource =
  Source.mkDOISource
    "Christin Scholz; Elisa C Baek; Matthew Brook O'Donnell; Hyun Suk Kim; Joseph N Cappella; Emily B Falk"
    "A neural model of valuation and information virality"
    "Proceedings of the National Academy of Sciences 114(11):2881-2886"
    "2017"
    "10.1073/pnas.1615259114"
    "https://doi.org/10.1073/pnas.1615259114"
    Source.academicArticleSource
    "Pays fMRI-based prediction of population-level article sharing from value/self/social neural signals in two studies; the observed population outcome is sharing, not an intrinsic neural virality label for arbitrary content."
    Source.publicAttribution

chan2023SharingSource : Source.AttributedSource
chan2023SharingSource =
  Source.mkDOISource
    "Hang-Yee Chan; Christin Scholz; Danielle Cosme; Rebecca E Martin; Christian Benitez; Anthony Resnick; Jose Carreras-Tartak; Nicole Cooper; Alexandra M Paul; Emily B Falk"
    "Neural signals predict information sharing across cultures"
    "Proceedings of the National Academy of Sciences 120(44):e2313175120"
    "2023"
    "10.1073/pnas.2313175120"
    "https://doi.org/10.1073/pnas.2313175120"
    Source.academicArticleSource
    "Pays preregistered cross-cultural generalization of a brain-based information-sharing prediction model. It does not establish universal culture-invariant decoding of all sharing behavior."
    Source.publicAttribution

metaTRIBEv2Receipt : NeuroAISourceReceipt
metaTRIBEv2Receipt = neuro-ai-source-receipt metaTRIBEv2Source metaAuthoredNeuroAI fMRI
  "predictive encoding model for high-resolution fMRI responses to complex naturalistic stimuli"
  "prediction is retained as a measurement/model relation under the repository fMRI proxy boundary, not hidden-state identity"

metaBrain2QwertyReceipt : NeuroAISourceReceipt
metaBrain2QwertyReceipt = neuro-ai-source-receipt metaBrain2QwertySource metaAuthoredNeuroAI EEGMEG
  "non-invasive neural-to-text decoding under the reported experimental pipeline"
  "task-bounded decoding is not unrestricted mind reading"

metaNeuralSetReceipt : NeuroAISourceReceipt
metaNeuralSetReceipt = neuro-ai-source-receipt metaNeuralSetSource metaAuthoredNeuroAI multimodalNeuralRecordings
  "unified software/data interface across neural modalities and stimuli"
  "common software interface does not collapse measurement semantics"

metaNeuralBenchReceipt : NeuroAISourceReceipt
metaNeuralBenchReceipt = neuro-ai-source-receipt metaNeuralBenchSource metaAuthoredNeuroAI multimodalNeuralRecordings
  "benchmarking surface for neuro-AI model comparison"
  "benchmark score does not create clinical or mechanistic authority"

scholz2017ViralityReceipt : NeuroforecastingSourceReceipt
scholz2017ViralityReceipt = neuroforecasting-source-receipt scholz2017ViralitySource fMRI
  "objectively logged population-level sharing of New York Times articles"
  "value/self/social neural signals add predictive information for sharing outcomes"
  "this is independent academic neuroforecasting, not a Meta-authored virality model and not a universal content-virality oracle"

chan2023SharingReceipt : NeuroforecastingSourceReceipt
chan2023SharingReceipt = neuroforecasting-source-receipt chan2023SharingSource fMRI
  "population sharing of US news articles across US and Netherlands samples"
  "pre-registered brain-based models generalized across samples/cultures better than self-report alone"
  "cross-cultural generalization remains scoped to the studied paradigm and stimuli"

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

record FMRIProxyAttachment : Set where
  constructor fmri-proxy-attachment
  field
    governance : FMRI.FMRIConnectomeProxyGovernance
    sourceReceipt : NeuroAISourceReceipt
    proxyBoundaryRetained : Bool
    proxyBoundaryRetainedIsTrue : proxyBoundaryRetained ≡ true

metaTRIBEProxyAttachment : FMRIProxyAttachment
metaTRIBEProxyAttachment =
  fmri-proxy-attachment FMRI.canonicalFMRIConnectomeProxyGovernance metaTRIBEv2Receipt true refl

record DyadicObserverPluralityBridge : Set where
  constructor dyadic-observer-plurality-bridge
  field
    aliceSynthesis : Alice.AliceBrownThreadInquirySynthesis
    synchronyReceipt : GABA.SynchronyAttachmentAssociationReceipt
    adultObservationDoesNotEqualChildExperience : Bool
    adultObservationDoesNotEqualChildExperienceIsTrue :
      adultObservationDoesNotEqualChildExperience ≡ true
    dyadicMeasurementDoesNotCollapseParticipantVoices : Bool
    dyadicMeasurementDoesNotCollapseParticipantVoicesIsTrue :
      dyadicMeasurementDoesNotCollapseParticipantVoices ≡ true

canonicalDyadicObserverPluralityBridge : DyadicObserverPluralityBridge
canonicalDyadicObserverPluralityBridge =
  dyadic-observer-plurality-bridge
    Alice.canonicalAliceBrownThreadInquirySynthesis
    GABA.nguyen2024SynchronyAttachmentAssociation
    true refl true refl

record LevinMultiscaleSignalAnchor : Set where
  constructor levin-multiscale-signal-anchor
  field
    siState : Levin.SIState
    multiscaleBioelectricOwnerReused : Bool
    multiscaleBioelectricOwnerReusedIsTrue : multiscaleBioelectricOwnerReused ≡ true
    brainOnlyOntologyIntroduced : Bool
    brainOnlyOntologyIntroducedIsFalse : brainOnlyOntologyIntroduced ≡ false

canonicalLevinMultiscaleSignalAnchor : LevinMultiscaleSignalAnchor
canonicalLevinMultiscaleSignalAnchor =
  levin-multiscale-signal-anchor Levin.canonicalSIState true refl false refl

------------------------------------------------------------------------
-- BCI calibration as longitudinal adaptation / user-burden evidence.
------------------------------------------------------------------------

record BCICalibrationBurdenReceipt : Set where
  constructor bci-calibration-burden-receipt
  field
    source : Source.AttributedSource
    baselineReference : String
    updatedReference : String
    selfSupervisedPretrainingReference : String
    participantSpecificModels : Bool
    participantSpecificModelsIsTrue : participantSpecificModels ≡ true
    crossParticipantSuperiorityEstablished : Bool
    crossParticipantSuperiorityEstablishedIsFalse :
      crossParticipantSuperiorityEstablished ≡ false
    independentReplicationEstablished : Bool
    independentReplicationEstablishedIsFalse :
      independentReplicationEstablished ≡ false

neuralink2026CalibrationReceipt : BCICalibrationBurdenReceipt
neuralink2026CalibrationReceipt =
  bci-calibration-burden-receipt
    neuralink2026PretrainingSource
    "company-reported historical calibration averaged about 55 minutes/week, typically around 10 minutes/day"
    "company reports some participants now calibrate about 10 minutes/week, with some decoders remaining useful for weeks"
    "participant-specific self-supervised encoders pretrained on thousands of hours drawn from more than 50,000 hours of unlabeled everyday neural recordings across the programme"
    true refl false refl false refl

------------------------------------------------------------------------
-- Compartment/transport and experimental-design backprop.
------------------------------------------------------------------------

data NeurochemicalCompartment : Set where
  centralBrainMeasurement : NeurochemicalCompartment
  peripheralBloodMeasurement : NeurochemicalCompartment
  extracellularLocalMeasurement : NeurochemicalCompartment

data PeripheralCentralTransportPermission : Set where

peripheralCentralTransportNotAutomatic : PeripheralCentralTransportPermission → ⊥
peripheralCentralTransportNotAutomatic ()

record TransportExperimentRequirement : Set where
  constructor transport-experiment-requirement
  field
    sourceCompartment : NeurochemicalCompartment
    targetCompartment : NeurochemicalCompartment
    discoveryRoute : Snowball.DiscoveryRoute
    transportModelRequired : Bool
    transportModelRequiredIsTrue : transportModelRequired ≡ true
    pairedMeasurementOrValidatedModelRequired : Bool
    pairedMeasurementOrValidatedModelRequiredIsTrue :
      pairedMeasurementOrValidatedModelRequired ≡ true
    pharmacokineticOrBiologicalMechanismRequired : Bool
    pharmacokineticOrBiologicalMechanismRequiredIsTrue :
      pharmacokineticOrBiologicalMechanismRequired ≡ true
    requirementReference : String

peripheralToCentralExperimentRequirement : TransportExperimentRequirement
peripheralToCentralExperimentRequirement =
  transport-experiment-requirement
    peripheralBloodMeasurement centralBrainMeasurement Snowball.experimentalDesign
    true refl true refl true refl
    "Backpropagate the blocked peripheral->central inference into an explicit experimental-design obligation: paired/linked compartments or a validated transport/PK/biological model with timing, dose/exposure, assay and population controls."

record NeuroforecastExperimentRequirement : Set where
  constructor neuroforecast-experiment-requirement
  field
    discoveryRoute : Snowball.DiscoveryRoute
    stimulusGeneralizationRequired : Bool
    stimulusGeneralizationRequiredIsTrue : stimulusGeneralizationRequired ≡ true
    outOfSamplePopulationOutcomeRequired : Bool
    outOfSamplePopulationOutcomeRequiredIsTrue : outOfSamplePopulationOutcomeRequired ≡ true
    selfReportComparatorRequired : Bool
    selfReportComparatorRequiredIsTrue : selfReportComparatorRequired ≡ true
    modalityAndPipelineFrozen : Bool
    modalityAndPipelineFrozenIsTrue : modalityAndPipelineFrozen ≡ true
    requirementReference : String

canonicalNeuroforecastExperimentRequirement : NeuroforecastExperimentRequirement
canonicalNeuroforecastExperimentRequirement =
  neuroforecast-experiment-requirement Snowball.experimentalDesign
    true refl true refl true refl true refl
    "Use held-out stimuli and population outcomes, preregistered/frozen neural ROIs or encoders, and explicit behavioral/self-report comparators before promoting a neuroforecasting relation beyond the acquired study family."

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record GABANeuroAIContextBoundary : Set where
  constructor gaba-neuro-ai-context-boundary
  field
    metaNeuroAIKeptDistinctFromIndependentViralityResearch : Bool
    metaNeuroAIKeptDistinctFromIndependentViralityResearchIsTrue :
      metaNeuroAIKeptDistinctFromIndependentViralityResearch ≡ true
    fmriPredictionDoesNotBecomeMindReading : Bool
    fmriPredictionDoesNotBecomeMindReadingIsFalse :
      fmriPredictionDoesNotBecomeMindReading ≡ false
    dyadicSignalsDoNotCollapseObserverPlurality : Bool
    dyadicSignalsDoNotCollapseObserverPluralityIsTrue :
      dyadicSignalsDoNotCollapseObserverPlurality ≡ true
    peripheralToCentralTransportAutomatic : Bool
    peripheralToCentralTransportAutomaticIsFalse :
      peripheralToCentralTransportAutomatic ≡ false
    neuralinkWeeklyCalibrationUniversal : Bool
    neuralinkWeeklyCalibrationUniversalIsFalse :
      neuralinkWeeklyCalibrationUniversal ≡ false
    blockedClaimsBackpropagateToExperimentalDesign : Bool
    blockedClaimsBackpropagateToExperimentalDesignIsTrue :
      blockedClaimsBackpropagateToExperimentalDesign ≡ true
    levinMultiscaleOwnerReused : Bool
    levinMultiscaleOwnerReusedIsTrue : levinMultiscaleOwnerReused ≡ true

canonicalGABANeuroAIContextBoundary : GABANeuroAIContextBoundary
canonicalGABANeuroAIContextBoundary =
  gaba-neuro-ai-context-boundary
    true refl false refl true refl false refl false refl true refl true refl
