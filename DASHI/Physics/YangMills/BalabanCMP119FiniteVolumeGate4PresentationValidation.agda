module DASHI.Physics.YangMills.BalabanCMP119FiniteVolumeGate4PresentationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FiniteVolumeGate4PresentationExact as P

round283CompilerClosed :
  P.cmp119Gate4Round283CompilerLevel ≡ machineChecked
round283CompilerClosed = refl

probabilityCompilerClosed :
  P.cmp119Gate4SelectedProbabilityCompilerLevel ≡ machineChecked
probabilityCompilerClosed = refl

finiteExpectationSameObjectRemainsPhysical :
  P.cmp119ToT5FiniteExpectationSameObjectLevel ≡ conditional
finiteExpectationSameObjectRemainsPhysical = refl
