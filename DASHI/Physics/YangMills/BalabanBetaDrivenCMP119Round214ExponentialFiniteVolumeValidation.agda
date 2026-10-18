module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ExponentialFiniteVolumeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ExponentialFiniteVolumeExact as P

round283CompilerOwned :
  P.betaDrivenRound214ExponentialRound283CompilerLevel ≡ machineChecked
round283CompilerOwned = refl

selectedProbabilityCompilerOwned :
  P.betaDrivenRound214ExponentialSelectedProbabilityCompilerLevel ≡ machineChecked
selectedProbabilityCompilerOwned = refl

t5ExpectationSameObjectRemainsPhysical :
  P.betaDrivenRound214ExponentialToT5ExpectationSameObjectLevel ≡ conditional
t5ExpectationSameObjectRemainsPhysical = refl
