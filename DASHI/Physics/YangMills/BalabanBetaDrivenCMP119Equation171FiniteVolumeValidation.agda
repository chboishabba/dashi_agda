module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Equation171FiniteVolumeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Equation171FiniteVolumeExact as P

round283CompilerOwned :
  P.betaDrivenEquation171Round283CompilerLevel ≡ machineChecked
round283CompilerOwned = refl

selectedProbabilityCompilerOwned :
  P.betaDrivenEquation171SelectedProbabilityCompilerLevel ≡ machineChecked
selectedProbabilityCompilerOwned = refl

t5ExpectationSameObjectRemainsPhysical :
  P.betaDrivenEquation171ToT5ExpectationSameObjectLevel ≡ conditional
t5ExpectationSameObjectRemainsPhysical = refl
