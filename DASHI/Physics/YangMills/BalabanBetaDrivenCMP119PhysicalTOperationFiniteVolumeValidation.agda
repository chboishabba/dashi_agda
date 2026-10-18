module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119PhysicalTOperationFiniteVolumeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119PhysicalTOperationFiniteVolumeExact as P

round283CompilerOwned :
  P.betaDrivenCMP119Round283CompilerLevel ≡ machineChecked
round283CompilerOwned = refl

selectedProbabilityCompilerOwned :
  P.betaDrivenCMP119SelectedProbabilityCompilerLevel ≡ machineChecked
selectedProbabilityCompilerOwned = refl

t5ExpectationSameObjectStillPhysical :
  P.betaDrivenCMP119ToT5ExpectationSameObjectLevel ≡ conditional
t5ExpectationSameObjectStillPhysical = refl
