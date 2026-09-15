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

s2bRadialSuffixStillOpen :
  Subject.s2bRadialSuffixRealizationRecovered ≡ false
s2bRadialSuffixStillOpen = Subject.s2bRadialSuffixRealizationRecoveredIsFalse

s2QuantitativeEstimateStillOpen :
  Subject.s2QuantitativeEstimateRecovered ≡ false
s2QuantitativeEstimateStillOpen = Subject.s2QuantitativeEstimateRecoveredIsFalse
