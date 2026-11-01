module DASHI.ComputerScience.RSA260BidiRawRankCrossValidationAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecCrossValidationExact as Cross
import DASHI.ComputerScience.RSA260BidiDegreeRawRankMinimalFrontierExact as Frontier

------------------------------------------------------------------------
-- RAW-RANK CROSS-VALIDATION ACQUISITION GAP
--
-- The existing 12-run hybrid-codec cross-validation receipt pays exact replay
-- and compression statistics over independent projection seeds/adapters, but its
-- formal owner does not retain per-run generator degree or coefficient-layer
-- ranks.  Therefore it cannot, by itself, validate the newer finite receipt
-- observer (degree, rank F2, rank F3, rank F4).
--
-- This owner records that distinction explicitly.  The next payment is to
-- reacquire or recompute those per-run coordinates from the same synthetic
-- generator runs, then test the observer on the independent seed portfolio.
------------------------------------------------------------------------

crossValidationReceipt : Cross.HybridCodecCrossValidationRuntimeReceipt
crossValidationReceipt = Cross.currentHybridCodecCrossValidationRuntimeReceipt

frontierBoundary : Frontier.DegreeRawRankMinimalFrontierBoundary
frontierBoundary = Frontier.canonicalDegreeRawRankMinimalFrontierBoundary

record RawRankCrossValidationAcquisitionBoundary : Set where
  constructor raw-rank-cross-validation-acquisition-boundary
  field
    twelveRunCodecCrossValidationExists : Bool
    twelveRunCrossValidationUsesIndependentProjectionSeeds : Bool
    twelveRunCrossValidationUsesPreparationAdapters : Bool
    aggregateRoundTripStatisticsRetained : Bool
    aggregateCompressionStatisticsRetained : Bool
    perRunGeneratorDegreeRetainedInCurrentFormalReceipt : Bool
    perRunRankF2F3F4RetainedInCurrentFormalReceipt : Bool
    degreeRawRankTripleCrossValidatedOnIndependentSeeds : Bool
    missingCoordinatesMayBeReacquiredFromSameSyntheticRuns : Bool
    productionRSA260Claimed : Bool
open RawRankCrossValidationAcquisitionBoundary public

canonicalRawRankCrossValidationAcquisitionBoundary :
  RawRankCrossValidationAcquisitionBoundary
canonicalRawRankCrossValidationAcquisitionBoundary =
  raw-rank-cross-validation-acquisition-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    true
    false

data RawRankCrossValidationAcquisitionResidual : Set where
  reacquireIndependentRunGeneratorDegrees : RawRankCrossValidationAcquisitionResidual
  reacquireIndependentRunRankF2F3F4 : RawRankCrossValidationAcquisitionResidual
  testDegreeRawRankTripleAcrossIndependentSeeds : RawRankCrossValidationAcquisitionResidual
  promoteOnlyIfNoConsumerCollisionRemains : RawRankCrossValidationAcquisitionResidual
  refineAgainIfIndependentCollisionAppears : RawRankCrossValidationAcquisitionResidual

firstRawRankCrossValidationAcquisitionResidual :
  RawRankCrossValidationAcquisitionResidual
firstRawRankCrossValidationAcquisitionResidual = reacquireIndependentRunGeneratorDegrees
