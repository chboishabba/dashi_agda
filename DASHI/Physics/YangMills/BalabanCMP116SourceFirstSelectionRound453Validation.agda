{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SourceFirstSelectionRound453Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116SourceFirstSelectionRound453Exact as R453
open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedApplicationNotIndependent :
  R453.selectedR406ApplicationChosenIndependentlyFromCMP116Source ≡ false
selectedApplicationNotIndependent = refl

postHocApplicationWeldPruned :
  R453.postHocSourceToSelectedApplicationEqualityRequired ≡ false
postHocApplicationWeldPruned = refl

sourceFirstProjectionDefinitional :
  R453.sourceFirstProjectionIsDefinitional ≡ true
sourceFirstProjectionDefinitional = refl

sourceFirstCompilerMachineChecked :
  R453.round453SourceFirstSelectionCompilerLevel ≡ machineChecked
sourceFirstCompilerMachineChecked = refl
