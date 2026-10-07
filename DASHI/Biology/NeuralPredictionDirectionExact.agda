module DASHI.Biology.NeuralPredictionDirectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.GABANeuroAIContextSnowballExact as NeuroAI
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop
import DASHI.Wikimedia.IbrahimCannabisTerpeneEntourageMoleculeCrossPollinationExact as PKPD

------------------------------------------------------------------------
-- DIRECTION-TYPED NEURAL PREDICTION TAXONOMY
--
-- Four empirically useful arrows are deliberately kept noninterchangeable:
--   stimulus -> measured brain response       (encoding)
--   measured brain response -> text/language  (decoding)
--   intracortical signal -> intended action   (BCI decoding/control)
--   brain response to content -> population outcome (neuroforecasting)
--
-- High prediction accuracy on one arrow does not license another arrow.
------------------------------------------------------------------------

data NeuralPredictionDirection : Set where
  stimulusToBrainEncoding : NeuralPredictionDirection
  brainToLanguageDecoding : NeuralPredictionDirection
  brainToActionDecoding : NeuralPredictionDirection
  brainResponseToPopulationOutcome : NeuralPredictionDirection

data PredictionScope : Set where
  withinSubjectScope : PredictionScope
  heldOutSubjectScope : PredictionScope
  heldOutStimulusScope : PredictionScope
  crossPopulationScope : PredictionScope
  populationAggregateScope : PredictionScope

record DirectionalPredictionReceipt : Set where
  constructor directional-prediction-receipt
  field
    direction : NeuralPredictionDirection
    source : Source.AttributedSource
    scope : PredictionScope
    inputReference : String
    outputReference : String
    validationReference : String
    authorityBoundary : String

metaTRIBEDirectionalReceipt : DirectionalPredictionReceipt
metaTRIBEDirectionalReceipt =
  directional-prediction-receipt
    stimulusToBrainEncoding
    NeuroAI.metaTRIBEv2Source
    heldOutSubjectScope
    "naturalistic visual/audio/language stimuli plus model/context inputs"
    "predicted high-resolution fMRI response"
    "Meta reports zero-shot prediction across new subjects, languages and tasks in its reported evaluation"
    "Encoding prediction remains under FMRIConnectomeProxyGovernance; it is not thought identity, diagnosis, or unrestricted decoding."

metaBrain2QwertyDirectionalReceipt : DirectionalPredictionReceipt
metaBrain2QwertyDirectionalReceipt =
  directional-prediction-receipt
    brainToLanguageDecoding
    NeuroAI.metaBrain2QwertySource
    withinSubjectScope
    "non-invasive neural recordings during the reported sentence-decoding protocol"
    "decoded natural-language sentence/text representation"
    "reported end-to-end real-time decoding evaluation"
    "Task-bounded decoding does not license unrestricted mind reading or arbitrary hidden-state recovery."

neuralinkActionDirectionalReceipt : DirectionalPredictionReceipt
neuralinkActionDirectionalReceipt =
  directional-prediction-receipt
    brainToActionDecoding
    NeuroAI.neuralink2026PretrainingSource
    withinSubjectScope
    "participant-specific intracortical neural activity"
    "intended computer-control action / cursor decoder output"
    "company-reported participant-specific self-supervised pretraining and longitudinal decoder-use result"
    "Company result; participant-specific BCI decoding is not cross-participant universality or general thought decoding."

scholzNeuroforecastDirectionalReceipt : DirectionalPredictionReceipt
scholzNeuroforecastDirectionalReceipt =
  directional-prediction-receipt
    brainResponseToPopulationOutcome
    NeuroAI.scholz2017ViralitySource
    populationAggregateScope
    "fMRI responses to health-news articles in laboratory participants"
    "objective population-level article-sharing outcome"
    "out-of-sample/population neuroforecasting analysis reported by Scholz et al."
    "Scoped sharing prediction is not an intrinsic universal virality score and is not Meta-authored research."

------------------------------------------------------------------------
-- Additional acquisition: Meta brain/model convergence and learning-mechanism
-- separation. Similar representation does not identify the learning algorithm.
------------------------------------------------------------------------

metaBackpropMisalignmentSource : Source.AttributedSource
metaBackpropMisalignmentSource =
  Source.mkNoDOISource
    "Josephine Raugel; Max Seitzer; Marc Szafraniec; Huy V. Vo; Jérémy Rapin; Patrick Labatut; Piotr Bojanowski; Valentin Wyart; Jean Remi King"
    "Misalignment Between Backpropagation and the Hierarchy of Brain Responses to Images"
    "AI at Meta Research / arXiv"
    "2026"
    "https://ai.meta.com/research/publications/misalignment-between-backpropagation-and-the-hierarchy-of-brain-responses-to-images/"
    Source.institutionalSource
    "Pays Meta's reported finding that backpropagated gradients can predict fMRI/MEG responses in selected visual-cortical/temporal regimes while their spatial and temporal organization diverges from biologically plausible backpropagation. Prediction/alignment is therefore not mechanistic identity."
    Source.publicAttribution

metaBrainModelConvergenceReceipt : NeuroAI.NeuroAISourceReceipt
metaBrainModelConvergenceReceipt =
  NeuroAI.neuro-ai-source-receipt
    NeuroAI.metaBrainModelConvergenceSource
    NeuroAI.metaAuthoredNeuroAI
    NeuroAI.fMRIMEG
    "representational, topographical and temporal comparison of DINOv3-family representations with human ultra-high-field fMRI and MEG"
    "brain-model similarity varies with architecture/training/data and remains representational correspondence, not proof that model and brain compute or learn identically"

metaBackpropMisalignmentReceipt : NeuroAI.NeuroAISourceReceipt
metaBackpropMisalignmentReceipt =
  NeuroAI.neuro-ai-source-receipt
    metaBackpropMisalignmentSource
    NeuroAI.metaAuthoredNeuroAI
    NeuroAI.fMRIMEG
    "backpropagated gradients can predict selected fMRI and MEG signals while exhibiting spatial/temporal hierarchy misalignment"
    "neural predictability does not establish biologically implemented backpropagation"

record BrainModelMechanismBoundary : Set where
  constructor brain-model-mechanism-boundary
  field
    representationalSimilarityImpliesMechanisticIdentity : Bool
    representationalSimilarityImpliesMechanisticIdentityIsFalse :
      representationalSimilarityImpliesMechanisticIdentity ≡ false
    gradientPredictivityImpliesBiologicalBackprop : Bool
    gradientPredictivityImpliesBiologicalBackpropIsFalse :
      gradientPredictivityImpliesBiologicalBackprop ≡ false
    commonBenchmarkImpliesMeasurementEquivalence : Bool
    commonBenchmarkImpliesMeasurementEquivalenceIsFalse :
      commonBenchmarkImpliesMeasurementEquivalence ≡ false
    encodingAccuracyImpliesDecodingAuthority : Bool
    encodingAccuracyImpliesDecodingAuthorityIsFalse :
      encodingAccuracyImpliesDecodingAuthority ≡ false

canonicalBrainModelMechanismBoundary : BrainModelMechanismBoundary
canonicalBrainModelMechanismBoundary =
  brain-model-mechanism-boundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Dynamic-content neuroforecasting acquisition.
------------------------------------------------------------------------

motoki2020Source : Source.AttributedSource
motoki2020Source =
  Source.mkDOISource
    "Kosuke Motoki; Shinsuke Suzuki; Ryuta Kawashima; Motoaki Sugiura"
    "A Combination of Self-Reported Data and Social-Related Neural Measures Forecasts Viral Marketing Success on Social Media"
    "Journal of Interactive Marketing 52(1)"
    "2020"
    "10.1016/j.intmar.2020.06.003"
    "https://doi.org/10.1016/j.intmar.2020.06.003"
    Source.academicArticleSource
    "Pays a study of neural and self-report responses to commercial video advertisements and subsequent social-media sharing outcomes. It extends neuroforecasting from static news to a video-advertising context, not to arbitrary viral content."
    Source.publicAttribution

motoki2020VideoNeuroforecastReceipt : DirectionalPredictionReceipt
motoki2020VideoNeuroforecastReceipt =
  directional-prediction-receipt
    brainResponseToPopulationOutcome
    motoki2020Source
    populationAggregateScope
    "fMRI/social-related neural measures and self-report while participants viewed video advertisements"
    "aggregate social-media sharing / viral-marketing outcome"
    "reported forecasting model combining self-report and social-related neural measures"
    "Commercial-video result remains stimulus-, platform-, sample- and outcome-scoped; it does not provide a general-purpose virality oracle."

------------------------------------------------------------------------
-- Neuralink primary/secondary provenance split.
------------------------------------------------------------------------

insideBCI2026CalibrationSource : Source.AttributedSource
insideBCI2026CalibrationSource =
  Source.mkNoDOISource
    "Inside BCI"
    "Neuralink cuts some implant users' calibration from 10 minutes a day to 10 minutes a week"
    "Inside BCI"
    "2026"
    "https://insidebci.com/news/2026-10-03-neuralink-pretraining-50000-hours-brain-data-calibration-decoder-11-bps/"
    Source.newsSource
    "Secondary report of Neuralink's October 2026 update; supplies the precise reported burden figures (historically about 10 minutes/day and 55 minutes/week average; some participants about 10 minutes/week). It is not independent validation of the underlying trial result."
    Source.publicAttribution

record NeuralinkProvenanceSplit : Set where
  constructor neuralink-provenance-split
  field
    primarySource : Source.AttributedSource
    secondaryExactBurdenSource : Source.AttributedSource
    primaryPaidClaim : String
    secondaryPaidClaim : String
    exactBurdenNumbersAttributedToSecondary : Bool
    exactBurdenNumbersAttributedToSecondaryIsTrue :
      exactBurdenNumbersAttributedToSecondary ≡ true
    independentReplicationEstablished : Bool
    independentReplicationEstablishedIsFalse :
      independentReplicationEstablished ≡ false

canonicalNeuralinkProvenanceSplit : NeuralinkProvenanceSplit
canonicalNeuralinkProvenanceSplit =
  neuralink-provenance-split
    NeuroAI.neuralink2026PretrainingSource
    insideBCI2026CalibrationSource
    "Primary Neuralink update: >50,000 hours unlabeled neural data; self-supervised participant-specific encoders; decoders working for weeks without recalibration; 11.32 BPS reported."
    "Secondary Inside BCI report: prior routine about 10 min/day, average 55 min/week; some participants about 10 min/week after the reported pretraining change."
    true refl false refl

------------------------------------------------------------------------
-- Existing PK/PD methodology donor and exact experimental-design slots.
------------------------------------------------------------------------

record PeripheralCentralPKDesignBridge : Set where
  constructor peripheral-central-pk-design-bridge
  field
    existingPKPDDonor : PKPD.CannabisTerpeneParetoStep
    transportSlot : Cone.ExperimentalDesignSlot
    timeSlot : Cone.ExperimentalDesignSlot
    assaySlot : Cone.ExperimentalDesignSlot
    sourcePopulationSlot : Cone.ExperimentalDesignSlot
    doseExposureOrEndogenousLevelRequired : Bool
    doseExposureOrEndogenousLevelRequiredIsTrue :
      doseExposureOrEndogenousLevelRequired ≡ true
    pairedCompartmentOrValidatedTransportRequired : Bool
    pairedCompartmentOrValidatedTransportRequiredIsTrue :
      pairedCompartmentOrValidatedTransportRequired ≡ true
    donorChemistryTransferredAsIdentity : Bool
    donorChemistryTransferredAsIdentityIsFalse :
      donorChemistryTransferredAsIdentity ≡ false
    bridgeReference : String

peripheralCentralTransportSlot : Cone.ExperimentalDesignSlot
peripheralCentralTransportSlot = Cone.transportSlot

crossParticipantCalibrationSlot : Cone.ExperimentalDesignSlot
crossParticipantCalibrationSlot = Cone.sourcePopulationSlot

canonicalPeripheralCentralPKDesignBridge : PeripheralCentralPKDesignBridge
canonicalPeripheralCentralPKDesignBridge =
  peripheral-central-pk-design-bridge
    PKPD.fourthParetoStep
    Cone.transportSlot
    Cone.timeSlot
    Cone.assaySlot
    Cone.sourcePopulationSlot
    true refl true refl false refl
    "Reuses the existing PK/PD Pareto obligation shape: explicit exposure/formulation-or-endogenous-level context plus comparator/assay/timing; cannabis molecule semantics are not transferred to GABA."

record CrossParticipantBCIDesignMap : Set where
  constructor cross-participant-bci-design-map
  field
    sourcePopulationSlot : Cone.ExperimentalDesignSlot
    baselineSlot : Cone.ExperimentalDesignSlot
    endpointSlot : Cone.ExperimentalDesignSlot
    timeSlot : Cone.ExperimentalDesignSlot
    nuisanceSlot : Cone.ExperimentalDesignSlot
    backpropBoundary : Backprop.BlockedImplicationBackpropBoundary
    heldOutParticipantRequired : Bool
    heldOutParticipantRequiredIsTrue : heldOutParticipantRequired ≡ true
    matchedCalibrationBudgetRequired : Bool
    matchedCalibrationBudgetRequiredIsTrue : matchedCalibrationBudgetRequired ≡ true
    longitudinalDriftEndpointRequired : Bool
    longitudinalDriftEndpointRequiredIsTrue :
      longitudinalDriftEndpointRequired ≡ true

canonicalCrossParticipantBCIDesignMap : CrossParticipantBCIDesignMap
canonicalCrossParticipantBCIDesignMap =
  cross-participant-bci-design-map
    Cone.sourcePopulationSlot
    Cone.baselineMeasurementSlot
    Cone.endpointMeasurementSlot
    Cone.timeSlot
    Cone.nuisanceControlSlot
    Backprop.canonicalBlockedImplicationBackpropBoundary
    true refl true refl true refl

------------------------------------------------------------------------
-- Global anti-collapse boundary.
------------------------------------------------------------------------

record NeuralPredictionDirectionBoundary : Set where
  constructor neural-prediction-direction-boundary
  field
    encodingAndDecodingAreDistinct : Bool
    encodingAndDecodingAreDistinctIsTrue : encodingAndDecodingAreDistinct ≡ true
    languageAndActionDecodingAreDistinct : Bool
    languageAndActionDecodingAreDistinctIsTrue : languageAndActionDecodingAreDistinct ≡ true
    decodingAndNeuroforecastingAreDistinct : Bool
    decodingAndNeuroforecastingAreDistinctIsTrue :
      decodingAndNeuroforecastingAreDistinct ≡ true
    fMRIProxyGovernanceRetained : Bool
    fMRIProxyGovernanceRetainedIsTrue : fMRIProxyGovernanceRetained ≡ true
    neuralinkPrimarySecondaryProvenanceSplit : Bool
    neuralinkPrimarySecondaryProvenanceSplitIsTrue :
      neuralinkPrimarySecondaryProvenanceSplit ≡ true
    blockedTransfersBackpropagateToExactDesignSlots : Bool
    blockedTransfersBackpropagateToExactDesignSlotsIsTrue :
      blockedTransfersBackpropagateToExactDesignSlots ≡ true

canonicalNeuralPredictionDirectionBoundary : NeuralPredictionDirectionBoundary
canonicalNeuralPredictionDirectionBoundary =
  neural-prediction-direction-boundary true refl true refl true refl true refl true refl true refl
