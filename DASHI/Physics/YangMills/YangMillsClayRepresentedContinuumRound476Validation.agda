{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
open import DASHI.Physics.YangMills.CompactLieProofLevel

representationFirstCompilerMachineChecked :
  R476.round476RepresentationFirstCompilerLevel ≡ machineChecked
representationFirstCompilerMachineChecked = refl

expectationConstructionIsDefinitional :
  R476.modelChoiceExpectationEqualityIsDefinitional ≡ true
expectationConstructionIsDefinitional = refl

schwingerConstructionIsDefinitional :
  R476.modelChoiceSchwingerEqualityIsDefinitional ≡ true
schwingerConstructionIsDefinitional = refl

functionalAloneIsNotMeasure :
  R476.expectationFunctionalAloneIsCountablyAdditiveMeasure ≡ false
functionalAloneIsNotMeasure = refl

postHocWeldPruned :
  R476.postHocRepresentedMeasureExpectationWeldRequired ≡ false
postHocWeldPruned = refl
