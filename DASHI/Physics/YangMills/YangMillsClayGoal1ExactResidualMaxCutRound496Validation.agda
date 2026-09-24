{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualBoardCompilerMachineChecked :
  R496.round496ResidualMaxCutCompilerLevel ≡ machineChecked
residualBoardCompilerMachineChecked = refl

residualLeafCountIsThirtyEight :
  R496.residualLeafCount ≡ 38
residualLeafCountIsThirty = refl

constructorEqualitiesPruned :
  R496.constructorChoiceEqualitiesCountedAsResidualLeaves ≡ false
constructorEqualitiesPruned = refl

projectiveFallbackPruned :
  R496.projectiveProkhorovFallbackCountedAsResidualLeaf ≡ false
projectiveFallbackPruned = refl

coercivityFallbackPruned :
  R496.globalCoercivityFallbackCountedAsResidualLeaf ≡ false
coercivityFallbackPruned = refl

su2GenericPremisePruned :
  R496.su2ValidationCountedAsGenericCompactSimplePremise ≡ false
su2GenericPremisePruned = refl

printedJWilsonEqualityPruned :
  R496.printedJEqualsWilsonObservableCountedAsResidualLeaf ≡ false
printedJWilsonEqualityPruned = refl

wholeMeasureEqualityPruned :
  R496.wholeMeasureRecordEqualityCountedAsResidualLeaf ≡ false
wholeMeasureEqualityPruned = refl

noClayCompletionClaim :
  R496.clayCompletionClaimed ≡ false
noClayCompletionClaim = refl
