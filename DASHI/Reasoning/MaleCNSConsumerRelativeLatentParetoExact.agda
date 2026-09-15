module DASHI.Reasoning.MaleCNSConsumerRelativeLatentParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerFamilyRefinementKernelExact as Family
import DASHI.Reasoning.FibreRoutingRateDistortionInformationBottleneckSnowballExact as RateIB

------------------------------------------------------------------------
-- MALECNS CONSUMER-RELATIVE LATENT PARETO ORDER
--
-- Ranking is downstream of representation legality and consumer-family
-- adequacy. A low terminal MAE/R2/correlation score can compare candidates that
-- are already eligible for the declared consumer family; it cannot manufacture
-- an adequacy witness, physical identity, mechanistic realization, or adequacy
-- for a different consumer family.
------------------------------------------------------------------------

record ConsumerAdequateLatentCandidate
    {State Index : Set}
    (family : Family.ConsumerFamily State Index) : Set₁ where
  constructor consumer-adequate-latent-candidate
  field
    Code : Set
    encode : State → Code
    familyAdequacy : Family.FamilyFactorsThrough encode family
    latentDimension : Nat
    descriptionLength : Nat
    candidateLabel : String

open ConsumerAdequateLatentCandidate public

record ConsumerRelativeParetoCoordinates : Set where
  constructor consumer-relative-pareto-coordinates
  field
    latentDimensionCoordinate : Nat
    descriptionLengthCoordinate : Nat
    heldOutMetricVector : String
    replicatedMetricVector : String
    generalizationCoordinate : String
    metricSemantics : String

open ConsumerRelativeParetoCoordinates public

record RankedConsumerAdequateCandidate
    {State Index : Set}
    (family : Family.ConsumerFamily State Index) : Set₁ where
  constructor ranked-consumer-adequate-candidate
  field
    candidate : ConsumerAdequateLatentCandidate family
    coordinates : ConsumerRelativeParetoCoordinates

open RankedConsumerAdequateCandidate public

adequacyPrecedesParetoRanking :
  ∀ {State Index}
    {family : Family.ConsumerFamily State Index} →
  (ranked : RankedConsumerAdequateCandidate family) →
  Family.FamilyFactorsThrough
    (encode (candidate ranked))
    family
adequacyPrecedesParetoRanking ranked = familyAdequacy (candidate ranked)

------------------------------------------------------------------------
-- Rate-distortion / information-bottleneck donor remains the canonical source
-- for the scalar-distortion and relevance firewalls.
------------------------------------------------------------------------

rateDistortionBoundary : RateIB.FibreRateDistortionInformationBottleneckBoundary
rateDistortionBoundary = RateIB.canonicalFibreRateDistortionInformationBottleneckBoundary

consumerAdequacyNotReplacedByScalarDistortion :
  RateIB.consumerAdequacyNotReplacedByScalarDistortion rateDistortionBoundary ≡ true
consumerAdequacyNotReplacedByScalarDistortion = refl

informationBottleneckNotMechanism :
  RateIB.informationBottleneckNotMechanismClaim rateDistortionBoundary ≡ true
informationBottleneckNotMechanism = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data TerminalLossCreatesAdequacy : Set where
data LowerLossIdentifiesPhysicalLatent : Set where
data DiscoveryBestDimensionIsUniversalMinimum : Set where
data SameMAEImpliesSameRepresentation : Set where

terminalLossDoesNotCreateAdequacy : TerminalLossCreatesAdequacy → ⊥
terminalLossDoesNotCreateAdequacy ()

lowerLossDoesNotIdentifyPhysicalLatent : LowerLossIdentifiesPhysicalLatent → ⊥
lowerLossDoesNotIdentifyPhysicalLatent ()

discoveryBestDimensionDoesNotBecomeUniversalMinimum :
  DiscoveryBestDimensionIsUniversalMinimum → ⊥
discoveryBestDimensionDoesNotBecomeUniversalMinimum ()

sameMAEDoesNotIdentifyRepresentation : SameMAEImpliesSameRepresentation → ⊥
sameMAEDoesNotIdentifyRepresentation ()

------------------------------------------------------------------------
-- Explicit six-level interpretation order retained from the live programme.
------------------------------------------------------------------------

data EvaluationLayer : Set where
  fibreOntologyLayer : EvaluationLayer
  observerProjectionLayer : EvaluationLayer
  consumerAdequacyLayer : EvaluationLayer
  admissibilityLayer : EvaluationLayer
  generalizationDesignLayer : EvaluationLayer
  terminalLossLayer : EvaluationLayer

record EvaluationLayerBoundary : Set where
  constructor evaluation-layer-boundary
  field
    lossIsTerminalCoordinate : Bool
    lossDefinesFibreOntology : Bool
    lossDefinesObserverAdequacy : Bool
    lossCreatesAdmissibility : Bool
    heldOutDesignSeparateFromAdequacy : Bool
    identicalScalarLossImpliesIdenticalFoldResidualField : Bool

open EvaluationLayerBoundary public

canonicalEvaluationLayerBoundary : EvaluationLayerBoundary
canonicalEvaluationLayerBoundary =
  evaluation-layer-boundary true false false false true false

------------------------------------------------------------------------
-- Python execution frontier.
--
-- Source/certification remains split. The current dashiBRAIN head now has a
-- fresh discovery execution receipt for the training-structure-only latent
-- ladder, a persisted frozen encoder, and an observed structural-family digest.
-- Exact selected-row acquisition has searched all six source trials. No
-- independent registered latent replication or Agda kernel receipt is promoted.
------------------------------------------------------------------------

record PythonLatentExecutionFrontier : Set where
  constructor python-latent-execution-frontier
  field
    repository : String
    branch : String
    sourceCommit : String
    scorecardSource : String
    latentLadderSource : String
    frozenEncoderSource : String
    replicationRunnerSource : String
    pathBaselineSource : String
    identityAcquisitionReceiptPath : String
    searchedTrialCount : Nat
    depositedSelectedCount : Nat
    exactIdentityCount : Nat
    unresolvedIdentityCount : Nat
    allSixSourceTrialsSearched : Bool
    completeIdentityRecovery : Bool
    identityRecoveryImpliesReplication : Bool
    unresolvedIdentityRowsBlockDiscoveryLatentExecution : Bool
    pythonLatentSourceWritten : Bool
    pythonLatentRuntimeReceiptObserved : Bool
    frozenEncoderArtifactObserved : Bool
    frozenEncoderSameStructuralCarrierRequired : Bool
    sameRegionVocabularyAuthorizesLatentReuse : Bool
    structuralCarrierFingerprintRuntimeObserved : Bool
    independentTrialLatentReplicationObserved : Bool
    agdaKernelReceiptObserved : Bool
    interpretation : String

open PythonLatentExecutionFrontier public

currentPythonLatentExecutionFrontier : PythonLatentExecutionFrontier
currentPythonLatentExecutionFrontier =
  python-latent-execution-frontier
    "github.com/chboishabba/dashiBRAIN"
    "agent/malecns-real-benchmark-tranche"
    "5752ad525d707b70f483f6359f3b5f34efff1586"
    "dashi/analysis/consumer_relative_scorecard.py"
    "dashi/analysis/structural_latent_ladder.py"
    "dashi/analysis/frozen_structural_latent_encoder.py"
    "scripts/run_malecns_replication_set.py"
    "dashi/analysis/structural_path_baselines.py"
    "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_identity_accumulation.json"
    6
    1620
    1209
    411
    true
    false
    false
    false
    true
    true
    true
    true
    false
    true
    false
    false
    "All six Gauthey LBM source trials have been searched under exact trace-identity recovery: 1209/1620 deposited selected rows are paid and 411 remain unresolved. Fresh a2_r5 discovery execution now observes the training-structure-only latent ladder, persists the frozen encoder, and records the exact structural-family SHA-256 prerequisite for reuse. This pays discovery runtime/fingerprint observation only; it does not pay independent latent replication, consumer-family adequacy, mechanism, universal minimum dimension, or Agda kernel certification."

------------------------------------------------------------------------
-- Observed discovery runtime receipt.
--
-- d=2 has the lowest observed MAE in the fresh discovery ladder. It does not
-- dominate the sender-gain carrier across all reported metrics: mP has slightly
-- better R², so the two remain a terminal-metric tradeoff rather than a scalar
-- promotion from mP to Z₂.
------------------------------------------------------------------------

record PythonLatentDiscoveryRuntimeReceipt : Set where
  constructor python-latent-discovery-runtime-receipt
  field
    runtimeCommit : String
    discoveryTrial : String
    runtimeReceiptPath : String
    frozenEncoderArtifactPath : String
    structuralCarrierSha256 : String
    d1MAE : String
    d1R2 : String
    d1Pearson : String
    d1MeanVarianceFraction : String
    d2MAE : String
    d2R2 : String
    d2Pearson : String
    d2MeanVarianceFraction : String
    d8MAE : String
    d8R2 : String
    d8Pearson : String
    d8MeanVarianceFraction : String
    zeroPredictionMAE : String
    senderGainMAE : String
    senderGainR2 : String
    d2LowestObservedMAE : Bool
    d2DominatesSenderGainAcrossReportedMetrics : Bool
    senderGainRemainsParetoTradeoff : Bool
    discoveryBestDimensionPromotesUniversalMinimum : Bool
    independentReplicationPaid : Bool
    agdaKernelReceiptPaid : Bool
    interpretation : String

open PythonLatentDiscoveryRuntimeReceipt public

currentPythonLatentDiscoveryRuntimeReceipt : PythonLatentDiscoveryRuntimeReceipt
currentPythonLatentDiscoveryRuntimeReceipt =
  python-latent-discovery-runtime-receipt
    "5752ad525d707b70f483f6359f3b5f34efff1586"
    "04032024_6f_a2_r5"
    "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_local_fibre_hyperfabric_latent.json"
    "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_local_fibre_hyperfabric_latent_encoder.npz"
    "f2db278a4790e4c1b397845ef6a4aeea9e2fb9cd606f6613e1faaa2412a6cf00"
    "0.132517"
    "-0.008609"
    "-0.19256"
    "0.82676"
    "0.131358"
    "-0.000624"
    "0.06384"
    "0.90787"
    "0.136395"
    "-0.068988"
    "-0.03545"
    "1.00000"
    "0.131961"
    "0.13189851095808636"
    "-0.000239"
    true
    false
    true
    false
    false
    false
    "The observed discovery ladder is consumer-relative. Z2 has the lowest observed MAE, while sender-gain mP retains slightly better R2; neither terminal metric vector authorizes representation identity, universal sufficiency, mechanism, or population minimality. The frozen encoder and structural digest are runtime-observed and are now eligible for same-carrier independent-recording evaluation."

------------------------------------------------------------------------
-- Aggregate boundary.
------------------------------------------------------------------------

record MaleCNSConsumerRelativeLatentParetoBoundary : Set where
  constructor malecns-consumer-relative-latent-pareto-boundary
  field
    consumerFamilyAdequacyPrecedesRanking : Bool
    consumerFamilyAdequacyPrecedesRankingIsTrue :
      consumerFamilyAdequacyPrecedesRanking ≡ true

    dimensionIsRankingCoordinateAfterAdequacy : Bool
    dimensionIsRankingCoordinateAfterAdequacyIsTrue :
      dimensionIsRankingCoordinateAfterAdequacy ≡ true

    descriptionLengthIsRankingCoordinateAfterAdequacy : Bool
    descriptionLengthIsRankingCoordinateAfterAdequacyIsTrue :
      descriptionLengthIsRankingCoordinateAfterAdequacy ≡ true

    terminalMetricVectorIsRepresentationAuthority : Bool
    terminalMetricVectorIsRepresentationAuthorityIsFalse :
      terminalMetricVectorIsRepresentationAuthority ≡ false

    discoveryLatentDimensionIsPopulationMinimum : Bool
    discoveryLatentDimensionIsPopulationMinimumIsFalse :
      discoveryLatentDimensionIsPopulationMinimum ≡ false

    frozenEncoderRequiresIndependentRecordingForReplication : Bool
    frozenEncoderRequiresIndependentRecordingForReplicationIsTrue :
      frozenEncoderRequiresIndependentRecordingForReplication ≡ true

    sameStructuralCarrierRequiredForFrozenReuse : Bool
    sameStructuralCarrierRequiredForFrozenReuseIsTrue :
      sameStructuralCarrierRequiredForFrozenReuse ≡ true

    sameRegionVocabularyAuthorizesFrozenReuse : Bool
    sameRegionVocabularyAuthorizesFrozenReuseIsFalse :
      sameRegionVocabularyAuthorizesFrozenReuse ≡ false

    lowerLossPromotesMechanism : Bool
    lowerLossPromotesMechanismIsFalse :
      lowerLossPromotesMechanism ≡ false

    observedD2MAEOptimumPromotesUniversalMinimum : Bool
    observedD2MAEOptimumPromotesUniversalMinimumIsFalse :
      observedD2MAEOptimumPromotesUniversalMinimum ≡ false

    senderGainAndD2RemainMetricTradeoff : Bool
    senderGainAndD2RemainMetricTradeoffIsTrue :
      senderGainAndD2RemainMetricTradeoff ≡ true

    interpretation : String

open MaleCNSConsumerRelativeLatentParetoBoundary public

canonicalMaleCNSConsumerRelativeLatentParetoBoundary :
  MaleCNSConsumerRelativeLatentParetoBoundary
canonicalMaleCNSConsumerRelativeLatentParetoBoundary =
  malecns-consumer-relative-latent-pareto-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    "MaleCNS latent search is consumer-relative and same-object constrained. Fresh discovery runtime now places Z2 and sender-gain mP on a terminal-metric tradeoff frontier: Z2 has lower MAE, while mP has slightly better R2. Frozen latent reuse requires the exact structural-family carrier, not merely the same region labels. Discovery-optimal dimension remains a candidate compression frontier, not universal sufficiency or physical-state dimensionality."
