module DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact as R

physicalActionToTOperationCompilerOwned :
  R.cmp119PhysicalActionToTOperationCompilerLevel ≡ machineChecked
physicalActionToTOperationCompilerOwned = refl

physicalTOperationAssemblyCompilerOwned :
  R.cmp119PhysicalTOperationAssemblyCompilerLevel ≡ machineChecked
physicalTOperationAssemblyCompilerOwned = refl

selectedActionGeneratedRemainsPhysical :
  R.literalCMP119SelectedActionIsGeneratedPhysicalActionLevel ≡ conditional
selectedActionGeneratedRemainsPhysical = refl

operationActionExponentialRemainsPhysical :
  R.literalCMP119OperationActionUsesSourceExponentialLevel ≡ conditional
operationActionExponentialRemainsPhysical = refl

negativeLogBackendRemainsPhysical :
  R.physicalNegativeLogExponentialBackendLevel ≡ conditional
negativeLogBackendRemainsPhysical = refl

strictSupportRemainsPhysical :
  R.literalCMP119PhysicalTOperationPositiveSupportLevel ≡ conditional
strictSupportRemainsPhysical = refl
