module DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitRegression where

------------------------------------------------------------------------
-- RED regression for the exact three-region S2b2 packet decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split

threeRegionBoundaryFluxIdentityClosedIsTrue :
  Split.threeRegionBoundaryFluxIdentityClosed ≡ true
threeRegionBoundaryFluxIdentityClosedIsTrue =
  Split.threeRegionBoundaryFluxIdentityClosedIsTrue

remoteIsNotUsedAsBooleanComplementIsTrue :
  Split.remoteIsNotUsedAsBooleanComplement ≡ true
remoteIsNotUsedAsBooleanComplementIsTrue =
  Split.remoteIsNotUsedAsBooleanComplementIsTrue

literalLowRemoteSpectralDatumConstructedIsFalse :
  Split.literalLowRemoteSpectralDatumConstructed ≡ false
literalLowRemoteSpectralDatumConstructedIsFalse =
  Split.literalLowRemoteSpectralDatumConstructedIsFalse
