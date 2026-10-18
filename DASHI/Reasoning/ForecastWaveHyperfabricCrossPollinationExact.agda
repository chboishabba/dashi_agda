module DASHI.Reasoning.ForecastWaveHyperfabricCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Physics.WaveProjectionLossAdapterExact as WaveProjection
import DASHI.Cognition.PNF.LLMWeightedFutureQuotientExact as WeightedFuture
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Hypervoxel

------------------------------------------------------------------------
-- FORECAST STATE x WAVE / HYPERFABRIC CROSS-POLLINATION
--
-- This bridge reuses the observation/projection mathematics developed in the
-- discrete-wave and hyperfabric lanes without identifying probabilistic
-- forecasting with quantum mechanics or with the Base369 ternary geometry.
--
-- The concrete exact result is dynamical non-sufficiency: two fine forecast
-- states can publish the same current probability surface and nevertheless
-- separate after a later update.  Hence the public probability alone need not
-- be a sufficient dynamical state.
------------------------------------------------------------------------

data ForecastFineState : Set where
  stableMechanismWeakEvidence : ForecastFineState
  unstableRegimeTransientEvidence : ForecastFineState

data PublishedProbabilitySurface : Set where
  samePublishedProbability : PublishedProbabilitySurface

data NextProbabilitySurface : Set where
  nextProbabilityLow : NextProbabilitySurface
  nextProbabilityHigh : NextProbabilitySurface

publishedProbabilityProjection :
  ForecastFineState → PublishedProbabilitySurface
publishedProbabilityProjection _ = samePublishedProbability

nextProbabilityObservation :
  ForecastFineState → NextProbabilitySurface
nextProbabilityObservation stableMechanismWeakEvidence = nextProbabilityLow
nextProbabilityObservation unstableRegimeTransientEvidence = nextProbabilityHigh

sameCurrentProbabilityDifferentNext :
  Coarse.ProjectionCollision
    publishedProbabilityProjection
    nextProbabilityObservation
sameCurrentProbabilityDifferentNext =
  Coarse.projectionCollision
    stableMechanismWeakEvidence
    unstableRegimeTransientEvidence
    refl
    (λ ())

currentProbabilityCannotDetermineNextProbability :
  (coarseObserve : PublishedProbabilitySurface → NextProbabilitySurface) →
  ((state : ForecastFineState) →
    nextProbabilityObservation state
      ≡ coarseObserve (publishedProbabilityProjection state)) →
  ⊥
currentProbabilityCannotDetermineNextProbability =
  Coarse.consumerCannotFactorThroughProjection
    sameCurrentProbabilityDifferentNext

------------------------------------------------------------------------
-- Weighted-future carrier alias.
--
-- The existing probabilistic/Nerode-like owner remains generic: forecast
-- applications may instantiate it only after the weight semantics are paid.
------------------------------------------------------------------------

ForecastWeightedFutureKernel :
  Set → Set → Set → Set₁
ForecastWeightedFutureKernel =
  WeightedFuture.WeightedFutureKernel

------------------------------------------------------------------------
-- Forecast explanation hyperfabric.
--
-- Local coordinates are typed and provenance-bearing.  A global explanation
-- would still need compatibility witnesses; the fabric by itself does not
-- create a causal story.
------------------------------------------------------------------------

data ForecastCoordinate : Set where
  evidenceCoordinate
  mechanismCoordinate
  regimeCoordinate
  temporalCoordinate
  resolutionCoordinate :
    ForecastCoordinate

data ForecastExplanationEdge : Set where
  explanationEdge : ForecastExplanationEdge

forecastCoordinateStalk : ForecastCoordinate → Set
forecastCoordinateStalk _ = String

forecastExplanationStalk : ForecastExplanationEdge → Set
forecastExplanationStalk _ = String

data ForecastIncidence :
  ForecastCoordinate → ForecastExplanationEdge → Set where
  evidenceIncident :
    ForecastIncidence evidenceCoordinate explanationEdge
  mechanismIncident :
    ForecastIncidence mechanismCoordinate explanationEdge
  regimeIncident :
    ForecastIncidence regimeCoordinate explanationEdge
  temporalIncident :
    ForecastIncidence temporalCoordinate explanationEdge
  resolutionIncident :
    ForecastIncidence resolutionCoordinate explanationEdge

restrictForecastCoordinate :
  ∀ {coordinate edge} →
  ForecastIncidence coordinate edge →
  forecastCoordinateStalk coordinate →
  forecastExplanationStalk edge
restrictForecastCoordinate _ value = value

forecastExplanationProvenance :
  ForecastExplanationEdge → List String
forecastExplanationProvenance explanationEdge =
  "forecast explanation edge retains evidence/mechanism/regime/time/resolution provenance"
  ∷ []

forecastExplanationSalience :
  ForecastExplanationEdge → Nat
forecastExplanationSalience explanationEdge = 5

forecastExplanationHyperfabric :
  Hyperfabric.TypedHyperfabric ForecastCoordinate ForecastExplanationEdge
forecastExplanationHyperfabric = record
  { vertexStalk = forecastCoordinateStalk
  ; edgeStalk = forecastExplanationStalk
  ; incidence = ForecastIncidence
  ; restrict = restrictForecastCoordinate
  ; edgeProvenance = forecastExplanationProvenance
  ; edgeSalience = forecastExplanationSalience
  ; fabricLabel = "forecast evidence/mechanism/regime/time/resolution hyperfabric"
  }

------------------------------------------------------------------------
-- Existing wave/hypervoxel owners are anchored explicitly.
------------------------------------------------------------------------

waveProjectionStatus :
  WaveProjection.WaveProjectionStatus
waveProjectionStatus =
  WaveProjection.waveProjectionStatus

hyperfabricAuthorityBoundary :
  Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricAuthorityBoundary =
  Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

hypervoxelGeometryBoundary :
  Hypervoxel.Ternary27HypervoxelGeometryBoundary
hypervoxelGeometryBoundary =
  Hypervoxel.canonicalTernary27HypervoxelGeometryBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ForecastWaveHyperfabricBoundary : Set where
  constructor forecast-wave-hyperfabric-boundary
  field
    scalarProbabilityIsCompleteFineState : Bool
    scalarProbabilityIsCompleteFineStateIsFalse :
      scalarProbabilityIsCompleteFineState ≡ false

    sameCurrentProbabilityForcesSameFuture : Bool
    sameCurrentProbabilityForcesSameFutureIsFalse :
      sameCurrentProbabilityForcesSameFuture ≡ false

    discreteWaveIsLiteralForecastProbability : Bool
    discreteWaveIsLiteralForecastProbabilityIsFalse :
      discreteWaveIsLiteralForecastProbability ≡ false

    hyperfabricAutomaticallyCreatesCausalExplanation : Bool
    hyperfabricAutomaticallyCreatesCausalExplanationIsFalse :
      hyperfabricAutomaticallyCreatesCausalExplanation ≡ false

    base369HypervoxelIsForecastOntology : Bool
    base369HypervoxelIsForecastOntologyIsFalse :
      base369HypervoxelIsForecastOntology ≡ false

    waveAndFabricSupplyReusableProjectionVocabulary : Bool
    waveAndFabricSupplyReusableProjectionVocabularyIsTrue :
      waveAndFabricSupplyReusableProjectionVocabulary ≡ true

canonicalForecastWaveHyperfabricBoundary :
  ForecastWaveHyperfabricBoundary
canonicalForecastWaveHyperfabricBoundary =
  forecast-wave-hyperfabric-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
