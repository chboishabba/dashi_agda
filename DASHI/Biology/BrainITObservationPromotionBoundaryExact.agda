module DASHI.Biology.BrainITObservationPromotionBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.BrainITSourceBoundaryExact as Source

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Reuse the existing repo witness that a coarse fMRI-like observation can
-- identify two distinct population states. This is the correct generic
-- firewall against reading Brain-IT as an inverse of the full neural state.

coarseObservationCollisionReused :
  Neural.fmriLikeObservation Neural.microActivationA
  ≡
  Neural.fmriLikeObservation Neural.microActivationB
coarseObservationCollisionReused = Neural.fmriProjectionCollision

microActivationsAreDistinct :
  Neural.microActivationA ≢ Neural.microActivationB
microActivationsAreDistinct ()

noUniversalMicroscopicRecovery :
  (recover : Neural.CoarseRegionalObservation → Neural.PopulationActivation) →
  ((x : Neural.PopulationActivation) →
    recover (Neural.fmriLikeObservation x) ≡ x) →
  ⊥
noUniversalMicroscopicRecovery recover section =
  microActivationsAreDistinct
    (trans
      (sym (section Neural.microActivationA))
      (trans
        (cong recover coarseObservationCollisionReused)
        (section Neural.microActivationB)))

reconstructionDoesNotRecoverMicroscopicState : Bool
reconstructionDoesNotRecoverMicroscopicState = true

viewedImageReconstructionDoesNotImplyArbitraryThoughtReading : Bool
viewedImageReconstructionDoesNotImplyArbitraryThoughtReading = true

nonInvasiveDoesNotImplyRemoteReadout : Bool
nonInvasiveDoesNotImplyRemoteReadout = true

record BrainITPromotionBoundary : Set where
  constructor brainITPromotionBoundary
  field
    imageReconstructionImpliesExactNeuralStateRecovery : Bool
    imageReconstructionImpliesExactNeuralStateRecoveryIsFalse :
      imageReconstructionImpliesExactNeuralStateRecovery ≡ false

    viewedStimulusDecoderImpliesArbitraryThoughtDecoder : Bool
    viewedStimulusDecoderImpliesArbitraryThoughtDecoderIsFalse :
      viewedStimulusDecoderImpliesArbitraryThoughtDecoder ≡ false

    noImplantImpliesNoScanner : Bool
    noImplantImpliesNoScannerIsFalse :
      noImplantImpliesNoScanner ≡ false

    scannerBasedImpliesRemotePointAndRead : Bool
    scannerBasedImpliesRemotePointAndReadIsFalse :
      scannerBasedImpliesRemotePointAndRead ≡ false

    sourceArbitraryThoughtBoundaryRetained :
      Source.arbitraryThoughtReadingSupported
        Source.canonicalBrainITSourceBoundary
      ≡ false

    sourceRemoteReadoutBoundaryRetained :
      Source.remotePointAtPersonReadingSupported
        Source.canonicalBrainITSourceBoundary
      ≡ false

canonicalBrainITPromotionBoundary : BrainITPromotionBoundary
canonicalBrainITPromotionBoundary =
  brainITPromotionBoundary
    false refl
    false refl
    false refl
    false refl
    refl
    refl
