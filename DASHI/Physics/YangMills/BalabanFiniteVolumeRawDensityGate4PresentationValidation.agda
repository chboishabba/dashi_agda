module DASHI.Physics.YangMills.BalabanFiniteVolumeRawDensityGate4PresentationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteVolumeRawDensityGate4PresentationExact as Raw

round283CompilerClosed :
  Raw.rawDensityGate4Round283CompilerLevel ≡ machineChecked
round283CompilerClosed = refl

probabilityCompilerClosed :
  Raw.rawDensityGate4SelectedProbabilityCompilerLevel ≡ machineChecked
probabilityCompilerClosed = refl

rawDensityFamilyRemainsPhysical :
  Raw.literalRawSlowDensityFamilyLevel ≡ conditional
rawDensityFamilyRemainsPhysical = refl

finiteExpectationSameObjectRemainsPhysical :
  Raw.finiteExpectationRawDensityMixtureSameObjectLevel ≡ conditional
finiteExpectationSameObjectRemainsPhysical = refl
