module DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact as Producer

-- Acceptance surface for the source-native F1 producer recut.

denseMarkedSourceDecayCompilerIsOwned :
  Producer.denseMarkedSourceDecayCompilerOwned ≡ true
denseMarkedSourceDecayCompilerIsOwned =
  Producer.denseMarkedSourceDecayCompilerOwnedIsTrue

linfinityJointDensityIsNotRequiredByThisRoute :
  Producer.fullJointDensityLinfinityRequiredByDenseMarkedRoute ≡ false
linfinityJointDensityIsNotRequiredByThisRoute =
  Producer.fullJointDensityLinfinityRequiredByDenseMarkedRouteIsFalse

sameObjectNormalizationWeldRemainsExplicit :
  Producer.sameObjectEnvelopeToPhysicalL2NormalizationStillRequired ≡ true
sameObjectNormalizationWeldRemainsExplicit =
  Producer.sameObjectEnvelopeToPhysicalL2NormalizationStillRequiredIsTrue

-- R295 now adapts directly to the generic marked-response/separation-decay ABI,
-- so this is no longer a separate post-R295 F1 payment.
selectedPhysicalMarkedDecayIsCompilerOutput :
  Producer.selectedPhysicalMarkedDecayProducerStillRequired ≡ false
selectedPhysicalMarkedDecayIsCompilerOutput =
  Producer.selectedPhysicalMarkedDecayProducerStillRequiredIsFalse

noClayPromotionFromCompilerAlone :
  Producer.clayPromotion ≡ false
noClayPromotionFromCompilerAlone = Producer.clayPromotionIsFalse
