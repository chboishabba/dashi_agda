module DASHI.Chemistry.CarbonForcingRateBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact as Carbon
import DASHI.Chemistry.DeepTimeCarbonPathResidualBidiExact as Path
import DASHI.Core.TrajectoryResidueExact as Residue

------------------------------------------------------------------------
-- CARBON FORCING RATE / CUMULATIVE TRANSFER BIDI
--
-- Equal cumulative transfer does not determine temporal profile.  The finite
-- fixture distinguishes a rapid pulse from a distributed transfer while keeping
-- the declared cumulative moved-carbon code fixed.  It is an information-
-- geometry witness, not a quantitative climate-response model.
------------------------------------------------------------------------

data TransferSchedule : Set where
  rapidPulse distributedTransfer : TransferSchedule

cumulativeMovedCarbon : TransferSchedule → Nat
cumulativeMovedCarbon _ = 4

data PeakRateClass : Set where
  highPeak lowerPeak : PeakRateClass

peakRateClass : TransferSchedule → PeakRateClass
peakRateClass rapidPulse = highPeak
peakRateClass distributedTransfer = lowerPeak

sameCumulativeTransfer :
  cumulativeMovedCarbon rapidPulse ≡ cumulativeMovedCarbon distributedTransfer
sameCumulativeTransfer = refl

peakRatesDiffer :
  peakRateClass rapidPulse ≡ peakRateClass distributedTransfer → ⊥
peakRatesDiffer ()

data ExposureHistoryClass : Set where
  abruptExposure gradualExposure : ExposureHistoryClass

exposureHistory : TransferSchedule → ExposureHistoryClass
exposureHistory rapidPulse = abruptExposure
exposureHistory distributedTransfer = gradualExposure

sameCumulativeTransferDoesNotRecoverExposureHistory :
  exposureHistory rapidPulse ≡ exposureHistory distributedTransfer → ⊥
sameCumulativeTransferDoesNotRecoverExposureHistory ()

record CarbonForcingRateReceipt : Set where
  constructor carbon-forcing-rate-receipt
  field
    cumulativeTransferReference : String
    timeGridReference : String
    fluxSeriesReference : String
    peakRateReference : String
    durationReference : String
    reservoirBoundaryReference : String
    responseTimescaleReference : String
    provenanceReference : String
    validationReference : String

carbonBoundary : Carbon.DeepTimeCarbonReservoirFluxBoundary
carbonBoundary = Carbon.canonicalDeepTimeCarbonReservoirFluxBoundary

pathBoundary : Path.DeepTimeCarbonPathResidualBoundary
pathBoundary = Path.canonicalDeepTimeCarbonPathResidualBoundary

record CarbonForcingRateBoundary : Set where
  constructor carbon-forcing-rate-boundary
  field
    equalCumulativeTransferImpliesEqualRateProfile : Bool
    equalCumulativeTransferImpliesEqualRateProfileIsFalse :
      equalCumulativeTransferImpliesEqualRateProfile ≡ false
    equalCumulativeTransferImpliesEqualExposureHistory : Bool
    equalCumulativeTransferImpliesEqualExposureHistoryIsFalse :
      equalCumulativeTransferImpliesEqualExposureHistory ≡ false
    rateProfileCanBeConsumerRelevantResidual : Bool
    rateProfileCanBeConsumerRelevantResidualIsTrue :
      rateProfileCanBeConsumerRelevantResidual ≡ true
    cumulativeBudgetAloneDeterminesEcologicalResponse : Bool
    cumulativeBudgetAloneDeterminesEcologicalResponseIsFalse :
      cumulativeBudgetAloneDeterminesEcologicalResponse ≡ false
    rateClaimNeedsTimeResolvedFluxReceipt : Bool
    rateClaimNeedsTimeResolvedFluxReceiptIsTrue :
      rateClaimNeedsTimeResolvedFluxReceipt ≡ true
    reading : String

canonicalCarbonForcingRateBoundary : CarbonForcingRateBoundary
canonicalCarbonForcingRateBoundary =
  carbon-forcing-rate-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    "Equal cumulative carbon transfer does not identify its temporal profile. A forcing-rate claim therefore requires a time-resolved flux receipt, and downstream ecological use must compare that rate/history against response and adaptation timescales rather than treating cumulative amount as the complete consumer state."
