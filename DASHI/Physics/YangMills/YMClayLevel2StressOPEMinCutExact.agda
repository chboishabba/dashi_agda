{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2StressOPEMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact as R87
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPECoeff
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact as OPERemainder
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery

------------------------------------------------------------------------
-- LEVEL-2 LITERAL CLAY STRESS/OPE MIN-CUT
--
-- After the R129 same-family recovery package is inhabited, the following are
-- already available on one literal continuum family:
--
--   * finite -> continuum measure recovery;
--   * literal Schwinger membership;
--   * the R127 OS -> literal-Schwinger weld;
--   * the literal stress source-derivative identification.
--
-- The remaining physical local-QFT theorem is therefore not "construct OS" and
-- not "prove stress-charge = H_OS".  The shortest existing owner is Round87 D:
--
--   SAME-family short-distance OPE / stress / AF identification
--
-- whose proof-bearing content is:
--
--   (1) identify the physical RG product remainder with the composite marked
--       tail on the SAME continuum family;
--   (2) identify the literal OPE coefficient coordinate with the SAME one-step
--       operator-mixing law and SAME UV normalization as the AF coefficient;
--   (3) prove the local translation Ward/stress law required by the literal
--       stress/OPE semantics.
--
-- Once (1) is supplied, geometric dyadic OPE decay is compiler-owned.
-- Once (2) is supplied, all-depth coefficient equality is compiler-owned.
-- Integral T00 = H_OS remains a stronger optional theorem.
------------------------------------------------------------------------

record Level2StressOPEPhysicalResidue : Set₁ where
  field
    SameFamilyPhysicalRGProductTailIdentification : Set
    sameFamilyPhysicalRGProductTailIdentification :
      SameFamilyPhysicalRGProductTailIdentification

    SameOneStepAFMixingAndUVNormalization : Set
    sameOneStepAFMixingAndUVNormalization :
      SameOneStepAFMixingAndUVNormalization

    LocalTranslationWardStressLaw : Set
    localTranslationWardStressLaw :
      LocalTranslationWardStressLaw

open Level2StressOPEPhysicalResidue public

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

r129RecoveryPaysR127AndStressDerivative : Bool
r129RecoveryPaysR127AndStressDerivative = true

r129RecoveryPaysR127AndStressDerivativeIsTrue :
  r129RecoveryPaysR127AndStressDerivative ≡ true
r129RecoveryPaysR127AndStressDerivativeIsTrue = refl

dyadicOPERemainderDecayIndependentAfterCompositeTailIdentification : Bool
dyadicOPERemainderDecayIndependentAfterCompositeTailIdentification = false

dyadicOPERemainderDecayIndependentAfterCompositeTailIdentificationIsFalse :
  dyadicOPERemainderDecayIndependentAfterCompositeTailIdentification ≡ false
dyadicOPERemainderDecayIndependentAfterCompositeTailIdentificationIsFalse = refl

allDepthOPECoefficientEqualityIndependentAfterOneStepLaw : Bool
allDepthOPECoefficientEqualityIndependentAfterOneStepLaw = false

allDepthOPECoefficientEqualityIndependentAfterOneStepLawIsFalse :
  allDepthOPECoefficientEqualityIndependentAfterOneStepLaw ≡ false
allDepthOPECoefficientEqualityIndependentAfterOneStepLawIsFalse = refl

stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCut : Bool
stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCut = false

stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCutIsFalse :
  stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCut ≡ false
stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCutIsFalse = refl

------------------------------------------------------------------------
-- Existing theorem levels.
------------------------------------------------------------------------

physicalR129RecoveryLevel : ProofLevel
physicalR129RecoveryLevel = Recovery.physicalR129SameFamilyRecoveryLevel

physicalRound87DLevel : ProofLevel
physicalRound87DLevel = R87.sameFamilyShortDistanceOPEStressAFLevel

dyadicOPERemainderCompilerLevel : ProofLevel
dyadicOPERemainderCompilerLevel =
  OPERemainder.sharedMarkedCompositeOPERemainderCompilerLevel

allDepthOPECoefficientCompilerLevel : ProofLevel
allDepthOPECoefficientCompilerLevel =
  OPECoeff.coefficientRGRecurrenceUniquenessLevel

level2StressOPEPhysicalMinCutLevel : ProofLevel
level2StressOPEPhysicalMinCutLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
