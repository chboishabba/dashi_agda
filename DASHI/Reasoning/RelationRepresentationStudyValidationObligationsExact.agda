module DASHI.Reasoning.RelationRepresentationStudyValidationObligationsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationRepresentationSourceRegistryExact as Sources

------------------------------------------------------------------------
-- SOURCE-BOUNDED STUDY VALIDATION OBLIGATIONS
--
-- PURPOSE
-- This module records what kinds of empirical artifacts would be needed to
-- independently reproduce/check the bounded claims made by the cited relation-
-- representation studies.  It does not claim that DASHI currently possesses
-- those artifacts, and it does not turn a paper's reported result into an Agda
-- theorem.
--
-- Attribution policy:
--   * author/title/venue/year/identifier are owned by the source registry;
--   * method-specific requirements below are derived from the cited study's
--     reported experimental design;
--   * DASHI adds the proof-carrying validation packaging itself;
--   * absent model weights, embeddings, activations, datasets, checkpoints,
--     seeds, preprocessing outputs, or raw score tables remain explicitly
--     unavailable rather than reconstructed from prose.
------------------------------------------------------------------------

data ValidationArtifact : Set where
  exactModelIdentity
  modelRevisionOrWeightHash
  tokenizerOrInputEncoding
  datasetIdentityAndVersion
  rawPairedExamples
  trainValidationTestSplit
  preprocessingReceipt
  layerOrRepresentationLocation
  rawEmbeddingsOrActivations
  fittedOperatorParameters
  baselineOperatorParameters
  metricImplementation
  rawPredictionOrSimilarityScores
  groundTruthOrHumanJudgments
  statisticalTestReceipt
  randomSeedsAndEnvironment
  codeRevision
  syntheticGenerationPromptAndModel
  deduplicationOrCollisionReceipt
  checkpointSeries
  weightOrParameterSnapshots
  spectralDiagnosticReceipt
  alternativeDiagnosticReceipt
  interventionTrajectory
  fittedGeometryOrManifold
  outputDistributionTrajectory
  compressionPartition
  compressionTolerance
  parameterCountOrCompressionRatio
  : ValidationArtifact

record StudyValidationProfile : Set where
  constructor studyValidationProfile
  field
    source : Sources.SourceReference
    methodReading : String
    requiredArtifacts : List ValidationArtifact
    reproducedClaimReading : String
    strongerClaimNotLicensed : String

open StudyValidationProfile public

------------------------------------------------------------------------
-- Christ, Csiszárik, Becsó, Varga (NeurIPS 2025)
------------------------------------------------------------------------

christRelationDecoderValidation : StudyValidationProfile
christRelationDecoderValidation =
  studyValidationProfile
    Sources.christEtAl2025
    "To independently check the reported relation-decoder/property-structure result, preserve the exact transformer/model revision, relation-triplet datasets and splits, chosen transformer layer, fitted affine LRE matrices and biases, output head/tokenizer behavior, per-example top-1 faithfulness, cross-evaluation matrix, tensor-network configuration/compression parameters, and execution/code provenance."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ tokenizerOrInputEncoding
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ trainValidationTestSplit
    ∷ layerOrRepresentationLocation
    ∷ fittedOperatorParameters
    ∷ rawPredictionOrSimilarityScores
    ∷ parameterCountOrCompressionRatio
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit reproduction of affine decoder faithfulness, cross-relation evaluation, and compression/generalization curves on the declared models and relation datasets."
    "Even exact reproduction would not by itself establish that the fitted operators are complete semantic relations, causal mechanisms, or socially/normatively authoritative representations."

------------------------------------------------------------------------
-- Freenor & Alvarez (arXiv:2510.09790; submitted/under-review ICLR 2026
-- version observed separately, not promoted here to accepted publication).
------------------------------------------------------------------------

riseRotationValidation : StudyValidationProfile
riseRotationValidation =
  studyValidationProfile
    Sources.freenorAlvarez2025
    "To check RISE, preserve neutral/transformed sentence pairs and their language/transformation labels; exact embedding-model identities and revisions; embedding dimensions/normalization; train/test split; canonicalization rotors, tangent-space prototype and prediction procedure; MDV and Procrustes baselines; held-out predicted/target embeddings and rotor-alignment scores; and, for the synthetic corpus, generation prompts/model plus diversity/deduplication receipts."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ trainValidationTestSplit
    ∷ preprocessingReceipt
    ∷ rawEmbeddingsOrActivations
    ∷ fittedOperatorParameters
    ∷ baselineOperatorParameters
    ∷ rawPredictionOrSimilarityScores
    ∷ syntheticGenerationPromptAndModel
    ∷ deduplicationOrCollisionReceipt
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit recomputation of RISE canonicalization/prototype/prediction and held-out rotor-alignment relative to MDV and Procrustes on the declared datasets, languages, and embedding models."
    "Successful reproduction would support the bounded geometric-transfer claim only; it would not establish universal semantic rotation, a context-free ontology, or target-domain realization for contempt/flourishing."

------------------------------------------------------------------------
-- Xinbo Ai (2026), recos.
------------------------------------------------------------------------

recosValidation : StudyValidationProfile
recosValidation =
  studyValidationProfile
    Sources.ai2026
    "To check recos versus cosine/dot-product, preserve exact model checkpoints for Word2Vec, FastText, GloVe, BERT, SGPT, DPR, E5, BGE, GTE, SPECTER and CLIP-ViT; exact STS12-16, STS-B and SICK-R data/labels; preprocessing and embedding arrays; metric implementations; all model-dataset score tables; Spearman correlations; and reported paired statistical-analysis inputs."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ preprocessingReceipt
    ∷ rawEmbeddingsOrActivations
    ∷ metricImplementation
    ∷ rawPredictionOrSimilarityScores
    ∷ groundTruthOrHumanJudgments
    ∷ statisticalTestReceipt
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit recomputation of recos/cosine/dot scores, Spearman correlations, model-dataset win/loss counts, and the declared significance/robustness analyses."
    "A reproduced STS advantage would remain metric- and benchmark-relative; it would not prove semantic ontology, relation identity, consumer sufficiency, or normative adequacy."

------------------------------------------------------------------------
-- Parupudi (2025), OS / HTS.
------------------------------------------------------------------------

magnitudeAwareValidation : StudyValidationProfile
magnitudeAwareValidation =
  studyValidationProfile
    Sources.parupudi2025
    "To check OS/HTS, preserve exact model revisions, benchmark datasets/splits and targets, raw sentence embeddings, OS/HTS/cosine/dot-product implementations, task-wise prediction errors/MSE, and the reported paired significance-analysis inputs/results."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ trainValidationTestSplit
    ∷ rawEmbeddingsOrActivations
    ∷ metricImplementation
    ∷ rawPredictionOrSimilarityScores
    ∷ groundTruthOrHumanJudgments
    ∷ statisticalTestReceipt
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit task-by-task reproduction of magnitude-aware versus cosine/dot performance and the reported significance comparisons."
    "Even successful reproduction would establish only the reported task-relative metric behavior; it would not license a universal magnitude-aware semantic geometry."

------------------------------------------------------------------------
-- Tacheny (2026), calibrated cosine.
------------------------------------------------------------------------

calibratedSimilarityValidation : StudyValidationProfile
calibratedSimilarityValidation =
  studyValidationProfile
    Sources.tacheny2026
    "To check calibrated cosine, preserve the exact pretrained embedding model/revision, human similarity-judgment corpus and calibration/evaluation split, raw embeddings and cosine scores, fitted isotonic-regression map, calibrated scores, calibration-error/bias calculations, rank-correlation results, and perturbation-test outputs used for local stability."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ trainValidationTestSplit
    ∷ rawEmbeddingsOrActivations
    ∷ fittedOperatorParameters
    ∷ rawPredictionOrSimilarityScores
    ∷ groundTruthOrHumanJudgments
    ∷ statisticalTestReceipt
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit independent fitting of the monotone calibration map and recomputation of calibration, bias, rank-preservation and perturbation-stability claims."
    "Calibration success changes score interpretation, not automatically the underlying representation, relation realization, causal semantics, or normative authority."

------------------------------------------------------------------------
-- Wurgaft et al. (2026), manifold steering.
------------------------------------------------------------------------

manifoldSteeringValidation : StudyValidationProfile
manifoldSteeringValidation =
  studyValidationProfile
    Sources.wurgaftEtAl2026
    "To check manifold steering, preserve exact model/task revisions, activation extraction locations and arrays, output probability distributions, fitted activation and behavior manifolds including fitting hyperparameters, linear-steering baseline paths, manifold intervention trajectories, output-behavior trajectories, reverse optimization from behavior paths to activation paths, and complete seeds/code/environment provenance."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ rawPairedExamples
    ∷ trainValidationTestSplit
    ∷ layerOrRepresentationLocation
    ∷ rawEmbeddingsOrActivations
    ∷ fittedGeometryOrManifold
    ∷ fittedOperatorParameters
    ∷ baselineOperatorParameters
    ∷ interventionTrajectory
    ∷ outputDistributionTrajectory
    ∷ rawPredictionOrSimilarityScores
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit refitting the activation/behavior manifolds, replaying linear and manifold-respecting interventions, and checking the reported bidirectional alignment between activation-space and behavior-space trajectories."
    "A reproduced intervention result would not by itself prove that the fitted manifold is a semantic ontology, that every representation is smoothly manifold-like, or that the geometry realizes a social/ethical target."

------------------------------------------------------------------------
-- Dhiman, Passarella, Tribastone, Valerio (2026), approximate FDE compression.
------------------------------------------------------------------------

differentialEquivalenceValidation : StudyValidationProfile
differentialEquivalenceValidation =
  studyValidationProfile
    Sources.dhimanEtAl2026
    "To check approximate-FDE compression, preserve trained network architecture/weights, exact translation into the polynomial ODE representation, epsilon tolerance, computed aggregation partition/lumping, synthetic-system ground truth or public-regression dataset splits, compressed weights/model, parameter counts, predictive error, declared pruning baselines, plus code/seeds/environment."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ trainValidationTestSplit
    ∷ preprocessingReceipt
    ∷ fittedOperatorParameters
    ∷ compressionTolerance
    ∷ compressionPartition
    ∷ baselineOperatorParameters
    ∷ rawPredictionOrSimilarityScores
    ∷ parameterCountOrCompressionRatio
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit reconstruction of the approximate differential-equivalence partition and the compression/accuracy trade-off against the declared pruning baselines."
    "Approximate dynamical equivalence sufficient for the compression experiment would not establish semantic identity or preservation of every downstream consumer."

------------------------------------------------------------------------
-- Prakash & Martin (2026), anti-grokking / WeightWatcher.
--
-- Reported setup: long-run training for two canonical grokking systems
-- (three-layer MLP on a subset of MNIST and a transformer on modular addition),
-- checkpointed train/test behavior, WeightWatcher/HTSR diagnostics including
-- Correlation Traps and alpha, plus alternative diagnostics; the paper also
-- reports related large-model pathologies.  The profile below is limited to
-- reproducing those reported diagnostics and phase observations.
------------------------------------------------------------------------

grokkingDynamicValidation : StudyValidationProfile
grokkingDynamicValidation =
  studyValidationProfile
    Sources.prakashMartin2026
    "To check the reported anti-grokking result, preserve the exact MLP/transformer architectures and initializations, MNIST-subset and modular-addition dataset definitions/splits, complete long-training schedules and checkpoint series, weight/parameter snapshots, train/test accuracy trajectories, exact WeightWatcher version/configuration, empirical spectral-density/Correlation-Trap outputs, HTSR alpha trajectories, alternative diagnostic trajectories, seeds/environment, and code revision. Any large-model comparison additionally requires exact model/checkpoint identity and the diagnostic extraction settings used there."
    ( exactModelIdentity
    ∷ modelRevisionOrWeightHash
    ∷ datasetIdentityAndVersion
    ∷ trainValidationTestSplit
    ∷ preprocessingReceipt
    ∷ checkpointSeries
    ∷ weightOrParameterSnapshots
    ∷ rawPredictionOrSimilarityScores
    ∷ spectralDiagnosticReceipt
    ∷ alternativeDiagnosticReceipt
    ∷ randomSeedsAndEnvironment
    ∷ codeRevision
    ∷ [] )
    "These artifacts would permit replay of the extended training trajectories and independent checking of whether post-generalization test collapse co-occurs with the reported WeightWatcher spectral signals while training fit remains saturated."
    "Reproducing that phase pattern would not prove a universal grokking law, that Correlation Traps are the unique causal mechanism, or that one spectral diagnostic is a semantic/future-safety certificate for unrelated models."

------------------------------------------------------------------------
-- Readiness state: the studies tell us what to ask for; this repository branch
-- does not contain the corresponding external empirical payloads.
------------------------------------------------------------------------

record ExternalStudyPayloadAvailability : Set where
  constructor externalStudyPayloadAvailability
  field
    relationDecoderRawPayloadPresent : Bool
    riseRawPayloadPresent : Bool
    recosRawPayloadPresent : Bool
    magnitudeAwareRawPayloadPresent : Bool
    calibratedSimilarityRawPayloadPresent : Bool
    manifoldSteeringRawPayloadPresent : Bool
    differentialEquivalenceRawPayloadPresent : Bool
    grokkingRawPayloadPresent : Bool
    availabilityReading : String

currentExternalStudyPayloadAvailability : ExternalStudyPayloadAvailability
currentExternalStudyPayloadAvailability =
  externalStudyPayloadAvailability
    false false false false false false false false
    "The branch contains source-bounded method profiles and tiny synthetic producer receipts, but not the external studies' raw model/data/activation/checkpoint payloads required for independent empirical reproduction."

record StudyValidationBoundary : Set where
  constructor studyValidationBoundary
  field
    paperMethodDescriptionCountsAsRawReceipt : Bool
    paperMethodDescriptionCountsAsRawReceiptIsFalse :
      paperMethodDescriptionCountsAsRawReceipt ≡ false

    citedResultCountsAsIndependentReproduction : Bool
    citedResultCountsAsIndependentReproductionIsFalse :
      citedResultCountsAsIndependentReproduction ≡ false

    publicCodeWithoutPinnedModelDataEnvironmentClosesValidation : Bool
    publicCodeWithoutPinnedModelDataEnvironmentClosesValidationIsFalse :
      publicCodeWithoutPinnedModelDataEnvironmentClosesValidation ≡ false

    exactRawPayloadCouldPopulateProducerInterfaces : Bool
    exactRawPayloadCouldPopulateProducerInterfacesIsTrue :
      exactRawPayloadCouldPopulateProducerInterfaces ≡ true

canonicalStudyValidationBoundary : StudyValidationBoundary
canonicalStudyValidationBoundary =
  studyValidationBoundary false refl false refl false refl true refl
