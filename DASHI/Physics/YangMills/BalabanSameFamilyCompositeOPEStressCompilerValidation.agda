{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSameFamilyCompositeOPEStressCompilerValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyCompositeOPEStressCompilerExact as C
opeRemainderCompilerOwned :
  C.sameFamilyCompositeOPERemainderCompilerLevel ≡ machineChecked
opeRemainderCompilerOwned = refl
localPackageCompilerOwned :
  C.sameFamilyCompositeOPEStressCompilerLevel ≡ machineChecked
localPackageCompilerOwned = refl
compositeIdentificationStillPhysical :
  C.physicalCompositeSameObjectIdentificationLevel ≡ conditional
compositeIdentificationStillPhysical = refl
stressAFStillPhysical :
  C.physicalLocalStressAFIdentificationLevel ≡ conditional
stressAFStillPhysical = refl
