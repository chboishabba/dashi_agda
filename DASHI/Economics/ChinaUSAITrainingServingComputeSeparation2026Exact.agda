module DASHI.Economics.ChinaUSAITrainingServingComputeSeparation2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact as Transcript
import DASHI.Economics.AIEconomicUsefulWorkTimeSeriesExact as TimeSeries
import DASHI.Economics.AICriticalInfrastructurePoliticsCrossPollinationExact as Politics

------------------------------------------------------------------------
-- CHINA / US TRAINING-SERVING COMPUTE CALIBRATION, 2026
--
-- This owner does not infer national capability from chip stock alone.  It
-- separates finite model-training access from persistent hosted-serving
-- capacity and from the downstream compute redistribution enabled by open
-- weights.
------------------------------------------------------------------------

record SourceBackedTrainingServingCalibration : Set where
  constructor sourceBackedTrainingServingCalibration
  field
    transcriptBoundary : Transcript.YouTubeShortSourceBoundary
    epochGapReceipt : Transcript.TranscriptClaimReceipt
    moonshotCapacityReceipt : Transcript.TranscriptClaimReceipt
    deepSeekServingReceipt : Transcript.TranscriptClaimReceipt
    asmlFleetReceipt : Transcript.TranscriptClaimReceipt
    asmlChinaReceipt : Transcript.TranscriptClaimReceipt

    capabilityGapSourceClosed : Bool
    hostedServingCapacityConstraintSourceClosed : Bool
    boundedProductionServingFootprintSourceClosed : Bool
    euvFleetConcentrationSourceClosed : Bool

    fivePercentChipShareSourceClosed : Bool
    exactOpenWeightCausalResponseSourceClosed : Bool
    chipStockAloneExplainsCapabilityGap : Bool
    trainingCompletionImpliesServingCapacity : Bool

open SourceBackedTrainingServingCalibration public

canonicalSourceBackedTrainingServingCalibration :
  SourceBackedTrainingServingCalibration
canonicalSourceBackedTrainingServingCalibration =
  sourceBackedTrainingServingCalibration
    Transcript.canonicalYouTubeShortSourceBoundary
    Transcript.frontierGapReceipt
    Transcript.moonshotCapacityReceipt
    Transcript.deepSeekNodesReceipt
    Transcript.asmlCountReceipt
    Transcript.asmlChinaReceipt
    true true true true
    false false false false

------------------------------------------------------------------------
-- BIDI economic producer map.
------------------------------------------------------------------------

data TrainingServingClaim : Set where
  frontierCapabilityCloseDespiteComputeAsymmetry
  hostedServiceCapacityAdequate
  openWeightReleaseShiftsServingBurden
  exportControlExplainsCapabilityGap
  servingScarcityImpairsSubscriptionExpansion
  : TrainingServingClaim

data TrainingServingProducer : Set where
  chipStockProducer
  capabilityBenchmarkProducer
  hostedCapacityProducer
  openWeightDeploymentProducer
  exportControlCausalProducer
  subscriptionAndServingEconomicsProducer
  : TrainingServingProducer

requiredProducer : TrainingServingClaim → TrainingServingProducer
requiredProducer frontierCapabilityCloseDespiteComputeAsymmetry = capabilityBenchmarkProducer
requiredProducer hostedServiceCapacityAdequate = hostedCapacityProducer
requiredProducer openWeightReleaseShiftsServingBurden = openWeightDeploymentProducer
requiredProducer exportControlExplainsCapabilityGap = exportControlCausalProducer
requiredProducer servingScarcityImpairsSubscriptionExpansion = subscriptionAndServingEconomicsProducer

------------------------------------------------------------------------
-- Time-series implication: training compute and serving compute must be separate
-- monitored coordinates.  Raw national chip inventory is not a substitute for
-- compute per successful task or fully-loaded cost per successful task.
------------------------------------------------------------------------

data ChipInventoryImpliesUsefulWorkEconomicsPermission : Set where

data TrainingBenchmarkImpliesHostedUnitEconomicsPermission : Set where

data OpenWeightAvailabilityImpliesExternalDemandPermission : Set where

chipInventoryDoesNotAutoPromoteToUsefulWorkEconomics :
  ChipInventoryImpliesUsefulWorkEconomicsPermission → ⊥
chipInventoryDoesNotAutoPromoteToUsefulWorkEconomics ()

trainingBenchmarkDoesNotAutoPromoteToHostedUnitEconomics :
  TrainingBenchmarkImpliesHostedUnitEconomicsPermission → ⊥
trainingBenchmarkDoesNotAutoPromoteToHostedUnitEconomics ()

openWeightAvailabilityDoesNotAutoPromoteToExternalDemand :
  OpenWeightAvailabilityImpliesExternalDemandPermission → ⊥
openWeightAvailabilityDoesNotAutoPromoteToExternalDemand ()

usefulWorkUsageFirewall :
  TimeSeries.UsageGrowthDeterminesFutureClassPermission → ⊥
usefulWorkUsageFirewall = TimeSeries.usageGrowthDoesNotDetermineFutureClass

criticalInfrastructureHistoricalIdentityFirewall :
  Politics.PoliticsCrossPollinationImpliesHistoricalIdentityPermission → ⊥
criticalInfrastructureHistoricalIdentityFirewall =
  Politics.politicsCrossPollinationDoesNotAutoPromoteToHistoricalIdentity
