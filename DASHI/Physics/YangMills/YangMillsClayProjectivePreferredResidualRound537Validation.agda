{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayProjectivePreferredResidualRound537Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayProjectivePreferredResidualRound537Exact as R537
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualCountIsTwentySix :
  R537.residualLeafCount ≡ 26
residualCountIsTwentySix = refl

projectiveCompilerMachineChecked :
  R537.projectiveRepresentationCompilerLevel ≡ machineChecked
projectiveCompilerMachineChecked = refl

representedConvergenceMachineChecked :
  R537.representedConvergenceCompilerLevel ≡ machineChecked
representedConvergenceMachineChecked = refl

singleCutoffRepresentationPruned :
  R537.selectedIndexRepresentationStillPreferred ≡ false
singleCutoffRepresentationPruned = refl

noOpaqueEndpointSemantics :
  R537.opaqueEndpointSemanticLeavesRemaining ≡ false
noOpaqueEndpointSemantics = refl
