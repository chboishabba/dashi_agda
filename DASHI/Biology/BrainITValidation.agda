module DASHI.Biology.BrainITValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.BrainITSourceBoundaryExact as Source
import DASHI.Biology.BrainITFunctionalClusterTransferExact as Transfer
import DASHI.Biology.BrainITObservationPromotionBoundaryExact as Boundary

brainITMaxCutPinsSourceBoundary :
  Source.arbitraryThoughtReadingSupported Source.canonicalBrainITSourceBoundary
  ≡ false
brainITMaxCutPinsSourceBoundary = refl

brainITMaxCutPinsRemoteBoundary :
  Source.remotePointAtPersonReadingSupported Source.canonicalBrainITSourceBoundary
  ≡ false
brainITMaxCutPinsRemoteBoundary = refl

brainITMaxCutPinsSharedClusterCount :
  Transfer.functionalClusterCount Transfer.canonicalBrainITArchitecture ≡ 128
brainITMaxCutPinsSharedClusterCount = refl

brainITMaxCutPinsOneHourTransfer :
  Transfer.sourceReportsComparablePerformance Transfer.brainITOneHourTransfer
  ≡ true
brainITMaxCutPinsOneHourTransfer = refl

brainITMaxCutPinsObservationFirewall :
  Boundary.reconstructionDoesNotRecoverMicroscopicState ≡ true
brainITMaxCutPinsObservationFirewall = refl

brainITMaxCutPinsThoughtPromotionFirewall :
  Boundary.viewedImageReconstructionDoesNotImplyArbitraryThoughtReading ≡ true
brainITMaxCutPinsThoughtPromotionFirewall = refl
