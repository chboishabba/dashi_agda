module DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact as Producer

-- RED-first acceptance surface for the source-native F1 producer recut.
-- This validation intentionally lands before the production owner so the
-- required public contract is fixed before implementation.

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

selectedPhysicalMarkedDecayRemainsExplicit :
  Producer.selectedPhysicalMarkedDecayProducerStillRequired ≡ true
selectedPhysicalMarkedDecayRemainsExplicit =
  Producer.selectedPhysicalMarkedDecayProducerStillRequiredIsTrue

noClayPromotionFromCompilerAlone :
  Producer.clayPromotion ≡ false
noClayPromotionFromCompilerAlone = Producer.clayPromotionIsFalse
