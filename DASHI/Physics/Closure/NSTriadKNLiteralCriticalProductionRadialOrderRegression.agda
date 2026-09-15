module DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Subject

radialSortConstructed :
  Subject.literalRadialShellSortConstructed ≡ true
radialSortConstructed = Subject.literalRadialShellSortConstructedIsTrue

radialSortProvedOrdered :
  Subject.literalRadialShellOrderProved ≡ true
radialSortProvedOrdered = Subject.literalRadialShellOrderProvedIsTrue

radialSortPreservesExactModes :
  Subject.literalRadialShellSortPermutationClosed ≡ true
radialSortPreservesExactModes =
  Subject.literalRadialShellSortPermutationClosedIsTrue

weightedProductionInvariantUnderSort :
  Subject.literalWeightedProductionInvariantUnderRadialSort ≡ true
weightedProductionInvariantUnderSort =
  Subject.literalWeightedProductionInvariantUnderRadialSortIsTrue

suffixPacketSameObjectStillOpen :
  Subject.radialSuffixPhysicalPacketSameObjectClosed ≡ false
suffixPacketSameObjectStillOpen =
  Subject.radialSuffixPhysicalPacketSameObjectClosedIsFalse

quantitativeEstimateStillOpen :
  Subject.s2QuantitativePacketFluxEstimateClosed ≡ false
quantitativeEstimateStillOpen =
  Subject.s2QuantitativePacketFluxEstimateClosedIsFalse
