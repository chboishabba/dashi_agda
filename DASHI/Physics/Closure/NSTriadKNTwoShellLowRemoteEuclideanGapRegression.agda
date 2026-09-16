module DASHI.Physics.Closure.NSTriadKNTwoShellLowRemoteEuclideanGapRegression where

------------------------------------------------------------------------
-- RED regression for the finite two-shell Euclidean frequency gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNTwoShellLowRemoteEuclideanGapExact as Gap

lowFrequencyCeilingClosedIsTrue :
  Gap.lowFrequencyCeilingClosed ≡ true
lowFrequencyCeilingClosedIsTrue = Gap.lowFrequencyCeilingClosedIsTrue

remoteFrequencyFloorClosedIsTrue :
  Gap.remoteFrequencyFloorClosed ≡ true
remoteFrequencyFloorClosedIsTrue = Gap.remoteFrequencyFloorClosedIsTrue

literalLowRemoteSpectralDatumStillOpenIsFalse :
  Gap.literalLowRemoteSpectralDatumConstructed ≡ false
literalLowRemoteSpectralDatumStillOpenIsFalse =
  Gap.literalLowRemoteSpectralDatumConstructedIsFalse
