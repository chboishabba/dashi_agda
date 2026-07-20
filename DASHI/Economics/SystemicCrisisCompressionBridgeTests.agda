module DASHI.Economics.SystemicCrisisCompressionBridgeTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Bridge

closedModelReceipt : Bridge.ModelSelectionReceipt
closedModelReceipt =
  Bridge.modelReceipt true true true true true true true

openModelReceipt : Bridge.ModelSelectionReceipt
openModelReceipt =
  Bridge.modelReceipt true true true false true false true

stableResiduals : Bridge.ResidualDepthProfile
stableResiduals =
  Bridge.residualProfile neg neg neg neg neg neg

fracturedResiduals : Bridge.ResidualDepthProfile
fracturedResiduals =
  Bridge.residualProfile pos pos pos pos pos pos

activeObservation : Crisis.CrisisObservation
activeObservation =
  Crisis.observation pos pos pos pos pos neg neg

abatingObservation : Crisis.CrisisObservation
abatingObservation =
  Crisis.observation neg neg neg neg neg pos pos

activeChain : Bridge.TransmissionChain
activeChain =
  Bridge.transmission pos pos pos pos pos pos zer

sovereignChain : Bridge.TransmissionChain
sovereignChain =
  Bridge.transmission pos pos pos pos pos pos pos

activeObservedReceipt : Bridge.SystemicSignalReceipt
activeObservedReceipt =
  Bridge.systemicReceipt
    activeObservation
    fracturedResiduals
    activeChain
    openModelReceipt
    true true true

activeValidatedReceipt : Bridge.SystemicSignalReceipt
activeValidatedReceipt =
  Bridge.systemicReceipt
    activeObservation
    fracturedResiduals
    activeChain
    closedModelReceipt
    true true true

abatingReceipt : Bridge.SystemicSignalReceipt
abatingReceipt =
  Bridge.systemicReceipt
    abatingObservation
    stableResiduals
    sovereignChain
    closedModelReceipt
    true true true

fractureClassifies :
  Bridge.compressionRegime fracturedResiduals ≡ Bridge.fractureRegime
fractureClassifies = refl

stableClassifies :
  Bridge.compressionRegime stableResiduals ≡ Bridge.compressiveRegime
stableClassifies = refl

activeObservedDoesNotPretendValidation :
  Bridge.promotionLevel activeObservedReceipt ≡ Bridge.observedMechanismLevel
activeObservedDoesNotPretendValidation = refl

closedMDLPromotesValidatedModel :
  Bridge.promotionLevel activeValidatedReceipt ≡ Bridge.validatedModelLevel
closedMDLPromotesValidatedModel = refl

sovereignLinkIsSeparate :
  Bridge.sovereignTransmissionObserved activeChain ≡ false
sovereignLinkIsSeparate = refl

sovereignLinkCanClose :
  Bridge.sovereignTransmissionObserved sovereignChain ≡ true
sovereignLinkCanClose = refl

activePostureDominatesCompressionRegime :
  Bridge.monitoringPosture Crisis.activePhase Bridge.compressiveRegime
  ≡ Bridge.activeDysfunction
activePostureDominatesCompressionRegime = refl

abatingMechanicsDetected :
  Bridge.peakMechanicsObserved abatingReceipt ≡ true
abatingMechanicsDetected = refl

abatingStillDoesNotClaimPriceBottom :
  Bridge.priceBottomClaimed abatingReceipt ≡ false
abatingStillDoesNotClaimPriceBottom = refl

expectationReceiptCannotPromote :
  Bridge.promotionLevel
    (Bridge.expectationOnlyReceipt
      (Bridge.technologyExpectation Bridge.inflatedExpectations pos pos)
      closedModelReceipt)
  ≡ Bridge.unsupportedLevel
expectationReceiptCannotPromote = refl
