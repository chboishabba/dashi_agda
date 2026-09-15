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
-- This is deliberately source/certification split. The current dashiBRAIN head
-- contains source for normalized terminal scorecards, a training-structure-only
-- PCA latent ladder, a persisted frozen encoder, cross-recording frozen-encoder
-- evaluation, and a Turner-style inverse-weight shortest-path comparator. No
-- fresh runner receipt for this new tranche has been observed here yet.
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
    pythonLatentSourceWritten : Bool
    pythonLatentRuntimeReceiptObserved : Bool
    frozenEncoderArtifactObserved : Bool
    independentTrialLatentReplicationObserved : Bool
    agdaKernelReceiptObserved : Bool
    interpretation : String

open PythonLatentExecutionFrontier public

currentPythonLatentExecutionFrontier : PythonLatentExecutionFrontier
currentPythonLatentExecutionFrontier =
  python-latent-execution-frontier
    "github.com/chboishabba/dashiBRAIN"
    "agent/malecns-real-benchmark-tranche"
    "b6e1f514d26bcaebef2b1464176fc02046b268b0"
    "dashi/analysis/consumer_relative_scorecard.py"
    "dashi/analysis/structural_latent_ladder.py"
    "dashi/analysis/frozen_structural_latent_encoder.py"
    "scripts/run_malecns_replication_set.py"
    "dashi/analysis/structural_path_baselines.py"
    true
    false
    false
    false
    false
    "Source written only: terminal scorecards, structure-only Z_d ladder, durable frozen encoder and frozen-representation replicate path exist in Python source, but the new tests/real-data runner have not yet supplied an execution receipt. Existing earlier mP/hyperfabric receipts remain separate paid evidence."

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

    lowerLossPromotesMechanism : Bool
    lowerLossPromotesMechanismIsFalse :
      lowerLossPromotesMechanism ≡ false

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
    false refl
    "MaleCNS latent search is consumer-relative: first establish admissibility/factorisation for the declared consumer family, then compare dimension, description length and terminal held-out/replicated metrics. A discovery-recording Z_d curve is a candidate compression frontier, not universal sufficiency or physical-state dimensionality."
