{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Exact as R571
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R571.round571SourceFirstAllGroupCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

operationAlignmentPruned :
  R571.round571OperationAlignmentFieldsRequired ≡ false
operationAlignmentPruned = refl

fiveBlockAlignmentPruned :
  R571.round571FiveBlockPackageAlignmentRequired ≡ false
fiveBlockAlignmentPruned = refl

su2PromotionPruned :
  R571.round571SU2PromotionRequired ≡ false
su2PromotionPruned = refl
