module DASHI.Chemistry.DeepTimeCarbonPathResidualBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact as Carbon
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Core.HistoryConditionedChoiceExact as History

------------------------------------------------------------------------
-- DEEP-TIME CARBON PATH RESIDUAL
--
-- Equal final reservoir distributions need not imply equal exposure history.
-- The finite fixture contrasts a route which passes through an atmospheric
-- pulse with one which reaches the same final coarse ledger without that pulse.
-- This is an information-geometry witness, not a quantitative climate model.
------------------------------------------------------------------------

data CarbonRoute : Set where
  fossilViaAtmosphereToOcean
  fossilDirectBookkeepingToOcean
  : CarbonRoute

routeEndpoint : CarbonRoute → Carbon.CarbonLedger
routeEndpoint fossilViaAtmosphereToOcean = Carbon.afterOneOceanUptakeTransfer
routeEndpoint fossilDirectBookkeepingToOcean = Carbon.afterOneOceanUptakeTransfer

data AtmosphericPulseHistory : Set where
  atmosphericPulseOccurred
  noAtmosphericPulseInFixture
  : AtmosphericPulseHistory

routePulseHistory : CarbonRoute → AtmosphericPulseHistory
routePulseHistory fossilViaAtmosphereToOcean = atmosphericPulseOccurred
routePulseHistory fossilDirectBookkeepingToOcean = noAtmosphericPulseInFixture

routesShareFinalLedger :
  routeEndpoint fossilViaAtmosphereToOcean
  ≡ routeEndpoint fossilDirectBookkeepingToOcean
routesShareFinalLedger = refl

routesRetainDifferentPulseHistory :
  routePulseHistory fossilViaAtmosphereToOcean
  ≡ routePulseHistory fossilDirectBookkeepingToOcean → ⊥
routesRetainDifferentPulseHistory ()

data HistorySensitiveEcologyConsumer : Set where
  transientExposureRelevant
  noTransientExposureInFixture
  : HistorySensitiveEcologyConsumer

ecologyConsumer : CarbonRoute → HistorySensitiveEcologyConsumer
ecologyConsumer fossilViaAtmosphereToOcean = transientExposureRelevant
ecologyConsumer fossilDirectBookkeepingToOcean = noTransientExposureInFixture

sameEndpointDoesNotRecoverHistorySensitiveConsumer :
  ecologyConsumer fossilViaAtmosphereToOcean
  ≡ ecologyConsumer fossilDirectBookkeepingToOcean → ⊥
sameEndpointDoesNotRecoverHistorySensitiveConsumer ()

record CarbonPathResidualReceipt : Set where
  constructor carbon-path-residual-receipt
  field
    initialReservoirReference : String
    routeReference : String
    intermediateFluxReference : String
    peakExposureReference : String
    finalReservoirReference : String
    ecologicalMemoryReference : String
    provenanceReference : String
    validationReference : String

carbonBoundary : Carbon.DeepTimeCarbonReservoirFluxBoundary
carbonBoundary = Carbon.canonicalDeepTimeCarbonReservoirFluxBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

record DeepTimeCarbonPathResidualBoundary : Set where
  constructor deep-time-carbon-path-residual-boundary
  field
    sameFinalReservoirDistributionImpliesSameCarbonHistory : Bool
    sameFinalReservoirDistributionImpliesSameCarbonHistoryIsFalse :
      sameFinalReservoirDistributionImpliesSameCarbonHistory ≡ false
    sameFinalReservoirDistributionImpliesSameTransientExposure : Bool
    sameFinalReservoirDistributionImpliesSameTransientExposureIsFalse :
      sameFinalReservoirDistributionImpliesSameTransientExposure ≡ false
    carbonPathMayCarryEcologicallyRelevantResidual : Bool
    carbonPathMayCarryEcologicallyRelevantResidualIsTrue :
      carbonPathMayCarryEcologicallyRelevantResidual ≡ true
    endpointOnlyObserverCanBeInsufficientForHistorySensitiveConsumer : Bool
    endpointOnlyObserverCanBeInsufficientForHistorySensitiveConsumerIsTrue :
      endpointOnlyObserverCanBeInsufficientForHistorySensitiveConsumer ≡ true
    reading : String

canonicalDeepTimeCarbonPathResidualBoundary : DeepTimeCarbonPathResidualBoundary
canonicalDeepTimeCarbonPathResidualBoundary =
  deep-time-carbon-path-residual-boundary
    false refl
    false refl
    true refl
    true refl
    "Carbon-cycle endpoints do not generally erase trajectory information. The finite fixture reaches the same final reservoir ledger along two routes while retaining different atmospheric-pulse histories and therefore different history-sensitive consumer codes. Real climate/ecological use requires measured flux, timing and response receipts."
