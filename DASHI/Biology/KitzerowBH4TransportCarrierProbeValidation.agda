module DASHI.Biology.KitzerowBH4TransportCarrierProbeValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4TransportCarrierProbeExact as Probe

carrierQuestionIsContextSpecificNotUniversallyNegative :
  Probe.specificTransportersExistInSomeContexts Probe.canonicalTransportCarrierBoundary ≡ true
  × Probe.singleUniversalNeuralBH4CarrierEstablished Probe.canonicalTransportCarrierBoundary ≡ false
carrierQuestionIsContextSpecificNotUniversallyNegative = refl , refl

quantitativeTranscellularTransportIsPaidWithoutNeuralFluxPromotion :
  Probe.quantitativeTranscellularBH4RatePaid Probe.canonicalTransportCarrierBoundary ≡ true
  × Probe.quantitativeNeuralDonorRecipientFluxPaid Probe.canonicalTransportCarrierBoundary ≡ false
quantitativeTranscellularTransportIsPaidWithoutNeuralFluxPromotion = refl , refl

releaseUptakeAndCocultureDoNotBecomeMolecularTransferRate :
  Probe.catecholaminergicBH4ReleaseObserved Probe.canonicalTransportCarrierBoundary ≡ true
  × Probe.recipientBH4UptakeObserved Probe.canonicalTransportCarrierBoundary ≡ true
  × Probe.functionalCocultureCrossTalkObserved Probe.canonicalTransportCarrierBoundary ≡ true
  × Probe.releaseUptakeCocultureSufficesForQuantitativeTransfer Probe.canonicalTransportCarrierBoundary ≡ false
releaseUptakeAndCocultureDoNotBecomeMolecularTransferRate =
  refl , (refl , (refl , refl))

transportEvidenceDoesNotCloseAllocator :
  Probe.transportProbeClosesWholeAllocator Probe.canonicalTransportCarrierBoundary ≡ false
transportEvidenceDoesNotCloseAllocator = refl
