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

s2b1aPermutationRecovered :
  Subject.s2b1aRadialPermutationRecovered ≡ true
s2b1aPermutationRecovered = Subject.s2b1aRadialPermutationRecoveredIsTrue

s2b1aWeightedProductionInvariantRecovered :
  Subject.s2b1aWeightedProductionInvariantRecovered ≡ true
s2b1aWeightedProductionInvariantRecovered =
  Subject.s2b1aWeightedProductionInvariantRecoveredIsTrue

s2b1b0FullToNonzeroSelectorBridgeRecovered :
  Subject.s2b1b0FullToNonzeroSelectorBridgeRecovered ≡ true
s2b1b0FullToNonzeroSelectorBridgeRecovered =
  Subject.s2b1b0FullToNonzeroSelectorBridgeRecoveredIsTrue

s2b1b1UpperShellR98TransportRecovered :
  Subject.s2b1b1UpperShellR98TransportRecovered ≡ true
s2b1b1UpperShellR98TransportRecovered =
  Subject.s2b1b1UpperShellR98TransportRecoveredIsTrue

s2b1b2aCanonicalSuffixR98Recovered :
  Subject.s2b1b2aCanonicalSuffixR98Recovered ≡ true
s2b1b2aCanonicalSuffixR98Recovered =
  Subject.s2b1b2aCanonicalSuffixR98RecoveredIsTrue

s2b1bStructuralTailStillOpen :
  Subject.s2b1bStructuralSuffixRecovered ≡ false
s2b1bStructuralTailStillOpen =
  Subject.s2b1bStructuralSuffixRecoveredIsFalse

s2QuantitativeEstimateStillOpen :
  Subject.s2QuantitativeEstimateRecovered ≡ false
s2QuantitativeEstimateStillOpen = Subject.s2QuantitativeEstimateRecoveredIsFalse
