module DASHI.Physics.YangMills.BalabanClayT5ConfiguredDyadicTailSummationValidation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredDyadicTailSummationExact as Tail

finiteDyadicSummationIsMachineChecked :
  Tail.configuredDyadicFiniteSummationLevel ≡ machineChecked
finiteDyadicSummationIsMachineChecked = refl

pointwiseDefectSummationIsMachineChecked :
  Tail.configuredDefectFiniteTailCompilerLevel ≡ machineChecked
pointwiseDefectSummationIsMachineChecked = refl

literalDefectEstimateRemainsPhysical :
  Tail.literalOneStepDefectEstimateLevel ≡ conditional
literalDefectEstimateRemainsPhysical = refl

literalTelescopingIdentityRemainsPhysical :
  Tail.literalTelescopingIdentityLevel ≡ conditional
literalTelescopingIdentityRemainsPhysical = refl
