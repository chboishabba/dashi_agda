{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
open import DASHI.Physics.YangMills.CompactLieProofLevel

physicalProjectiveCompilerMachineChecked :
  R535.round535PhysicalProjectiveRepresentationCompilerLevel ≡ machineChecked
physicalProjectiveCompilerMachineChecked = refl

singleCutoffPathPruned :
  R535.selectedIndexRepresentationStillPreferred ≡ false
singleCutoffPathPruned = refl
