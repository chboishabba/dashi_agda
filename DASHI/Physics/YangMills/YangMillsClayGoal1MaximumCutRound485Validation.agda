{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1MaximumCutRound485Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayGoal1MaximumCutRound485Exact as R485
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R485.round485MaximumCutCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

projectiveFallbackPruned :
  R485.projectiveProkhorovMandatory ≡ false
projectiveFallbackPruned = refl

coerciveFallbackPruned :
  R485.globalCoerciveCompactnessRouteMandatory ≡ false
coerciveFallbackPruned = refl

positiveGapTokenPruned :
  R485.arbitraryPositiveGapTokenMandatory ≡ false
positiveGapTokenPruned = refl

noClayCompletionClaim :
  R485.clayCompletionClaimed ≡ false
noClayCompletionClaim = refl
