module DASHI.Physics.YangMills.BalabanClayT5TypedContinuumDefectCauchyValidation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5TypedContinuumDefectCauchyExact as Cauchy

absoluteFiniteDefectSummationIsCompilerOwned :
  Cauchy.typedAbsoluteDefectSummationLevel ≡ machineChecked
absoluteFiniteDefectSummationIsCompilerOwned = refl

typedTelescopingProducesCauchyModulus :
  Cauchy.typedTelescopingToCauchyCompilerLevel ≡ machineChecked
typedTelescopingProducesCauchyModulus = refl

fastRealRepresentativeIsCompilerOwned :
  Cauchy.typedExpectationFastRealCompilerLevel ≡ machineChecked
fastRealRepresentativeIsCompilerOwned = refl

absoluteOneStepDefectRemainsPhysical :
  Cauchy.physicalAbsoluteOneStepDefectLevel ≡ conditional
absoluteOneStepDefectRemainsPhysical = refl

typedTelescopingIdentityRemainsPhysical :
  Cauchy.physicalTypedTelescopingIdentityLevel ≡ conditional
typedTelescopingIdentityRemainsPhysical = refl

completionRemainsDownstream :
  Cauchy.completionOrTopologyRealizationAfterCauchyLevel ≡ conditional
completionRemainsDownstream = refl
