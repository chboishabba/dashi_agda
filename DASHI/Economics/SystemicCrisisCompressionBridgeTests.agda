module DASHI.Economics.SystemicCrisisCompressionBridgeTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Bridge

closedModelReceipt : Bridge.ModelSelectionReceipt
closedModelReceipt = Bridge.modelReceipt true true true true true true true

openModelReceipt : Bridge.ModelSelectionReceipt
openModelReceipt = Bridge.modelReceipt true true true false true false true

stableResiduals : Bridge.ResidualDepthProfile
stableResiduals = Bridge.residualProfile neg neg neg neg neg neg

fracturedResiduals : Bridge.ResidualDepthProfile
fracturedResiduals = Bridge.residualProfile pos pos pos pos pos pos

activeObservation : Crisis.CrisisObservation
activeObservation = Crisis.observation pos pos pos pos pos neg neg

abatingObservation : Crisis.CrisisObservation
abatingObservation = Crisis.observation neg neg neg neg neg pos pos

activeChain : Bridge.TransmissionChain
activeChain = Bridge.transmission pos pos pos pos pos pos zer

sovereignChain : Bridge.TransmissionChain
sovereignChain = Bridge.transmission pos pos pos pos pos pos pos

activeObservedReceipt : Bridge.SystemicSignalReceipt
activeObservedReceipt = Bridge.systemicReceipt activeObservation fracturedResiduals activeChain openModelReceipt true true true

activeValidatedReceipt : Bridge.SystemicSignalReceipt
activeValidatedReceipt = Bridge.systemicReceipt activeObservation fracturedResiduals activeChain closedModelReceipt true true true

abatingReceipt : Bridge.SystemicSignalReceipt
abatingReceipt = Bridge.systemicReceipt abatingObservation stableResiduals sovereignChain closedModelReceipt true true true

fractureClassifies : Bridge.compressionRegime fracturedResiduals ≡ Bridge.fractureRegime
fractureClassifies = refl

stableClassifies : Bridge.compressionRegime stableResiduals ≡ Bridge.compressiveRegime
stableClassifies = refl

observedBoundary : Bridge.promotionLevel activeObservedReceipt ≡ Bridge.observedMechanismLevel
observedBoundary = refl

validatedBoundary : Bridge.promotionLevel activeValidatedReceipt ≡ Bridge.validatedModelLevel
validatedBoundary = refl

sovereignLinkSeparate : Bridge.sovereignTransmissionObserved activeChain ≡ false
sovereignLinkSeparate = refl

sovereignLinkClosed : Bridge.sovereignTransmissionObserved sovereignChain ≡ true
sovereignLinkClosed = refl

activePosture : Bridge.monitoringPosture Crisis.activePhase Bridge.compressiveRegime ≡ Bridge.activeDysfunction
activePosture = refl

abatementDetected : Bridge.peakMechanicsObserved abatingReceipt ≡ true
abatementDetected = refl

noPriceBottomPromotion : Bridge.priceBottomClaimed abatingReceipt ≡ false
noPriceBottomPromotion = refl

expectationNonPromotion :
  Bridge.promotionLevel
    (Bridge.expectationOnlyReceipt
      (Bridge.technologyExpectation Bridge.inflatedExpectations pos pos)
      closedModelReceipt)
  ≡ Bridge.unsupportedLevel
expectationNonPromotion = refl
