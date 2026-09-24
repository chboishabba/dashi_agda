module DASHI.Physics.YangMills.BalabanFiniteVolumeConditionalGate4PresentationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteVolumeConditionalGate4PresentationExact as Conditional

round283CompilerClosed :
  Conditional.conditionalGate4Round283CompilerLevel ≡ machineChecked
round283CompilerClosed = refl

selectedProbabilityCompilerClosed :
  Conditional.conditionalGate4SelectedProbabilityCompilerLevel ≡ machineChecked
selectedProbabilityCompilerClosed = refl

slowLawFamilyRemainsPhysical :
  Conditional.physicalSlowFieldLawFamilyLevel ≡ conditional
slowLawFamilyRemainsPhysical = refl

finiteExpectationSameObjectRemainsPhysical :
  Conditional.finiteExpectationConditionalMixtureSameObjectLevel ≡ conditional
finiteExpectationSameObjectRemainsPhysical = refl
