{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
open import DASHI.Physics.YangMills.CompactLieProofLevel

generatorRepresentationMachineChecked :
  R547.round547CylinderGeneratorRepresentationCompilerLevel ≡ machineChecked
generatorRepresentationMachineChecked = refl

arbitraryObservableRepresentationNotAssumed :
  R547.arbitraryBoundedObservableRepresentationAssumed ≡ false
arbitraryObservableRepresentationNotAssumed = refl

selectedCylinderClassPreferred :
  R547.selectedCylinderClassRepresentationPreferred ≡ true
selectedCylinderClassPreferred = refl

selectedClosureRemainsPhysical :
  R547.literalRound547SelectedObservableClosureRepresentationLevel ≡ conditional
selectedClosureRemainsPhysical = refl
