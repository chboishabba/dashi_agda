module DASHI.Papers.NavierStokes.FourLaneProofProgramS2bBandTransferRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Papers.NavierStokes.FourLaneProofProgramS2bBandTransferAdapterExact as Subject

baseFourLaneCoordinatorReused :
  Subject.baseFourLaneCoordinatorReused ≡ true
baseFourLaneCoordinatorReused = Subject.baseFourLaneCoordinatorReusedIsTrue

s2b0BandTransferRecovered :
  Subject.s2b0LiteralBandTransferRecovered ≡ true
s2b0BandTransferRecovered = Subject.s2b0LiteralBandTransferRecoveredIsTrue

s2b1aRadialOrderRecovered :
  Subject.s2b1aRadialOrderRecovered ≡ true
s2b1aRadialOrderRecovered = Subject.s2b1aRadialOrderRecoveredIsTrue

s2b1aWeightedProductionInvariantRecovered :
  Subject.s2b1aWeightedProductionInvariantRecovered ≡ true
s2b1aWeightedProductionInvariantRecovered =
  Subject.s2b1aWeightedProductionInvariantRecoveredIsTrue

s2b1bRadialSuffixPacketStillOpen :
  Subject.s2b1bRadialSuffixPacketRecovered ≡ false
s2b1bRadialSuffixPacketStillOpen =
  Subject.s2b1bRadialSuffixPacketRecoveredIsFalse

s2QuantitativeEstimateStillOpen :
  Subject.s2QuantitativeEstimateRecovered ≡ false
s2QuantitativeEstimateStillOpen = Subject.s2QuantitativeEstimateRecoveredIsFalse
