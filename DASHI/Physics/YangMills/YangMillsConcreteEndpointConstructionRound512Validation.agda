{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteEndpointConstructionRound512Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsConcreteEndpointConstructionRound512Exact as R512
open import DASHI.Physics.YangMills.CompactLieProofLevel

endpointConstructionCompilerMachineChecked :
  R512.round512ConcreteEndpointConstructionCompilerLevel ≡ machineChecked
endpointConstructionCompilerMachineChecked = refl

continuumSchwingerSemanticsMachineChecked :
  R512.round512ContinuumAndSchwingerSemanticsCompilerLevel ≡ machineChecked
continuumSchwingerSemanticsMachineChecked = refl

osReconstructionSemanticsMachineChecked :
  R512.round512OSReconstructionSemanticsCompilerLevel ≡ machineChecked
osReconstructionSemanticsMachineChecked = refl

gapSemanticsMachineChecked :
  R512.round512GapSemanticsCompilerLevel ≡ machineChecked
gapSemanticsMachineChecked = refl

nontrivialitySemanticsMachineChecked :
  R512.round512NontrivialitySemanticsCompilerLevel ≡ machineChecked
nontrivialitySemanticsMachineChecked = refl
