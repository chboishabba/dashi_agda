{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticMeaningRound441Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticMeaningRound441Exact as R441
open import DASHI.Physics.YangMills.CompactLieProofLevel

concreteExpectationLimitCompilerMachineChecked :
  R441.round441ConcreteExpectationLimitCompilerLevel ≡ machineChecked
concreteExpectationLimitCompilerMachineChecked = refl

sameMeasureSchwingerCompilerMachineChecked :
  R441.round441SameMeasureSchwingerCompilerLevel ≡ machineChecked
sameMeasureSchwingerCompilerMachineChecked = refl

independentContinuumWitnessPruned :
  R441.round441IndependentContinuumExistenceWitnessRequired ≡ false
independentContinuumWitnessPruned = refl

independentSchwingerWitnessPruned :
  R441.round441IndependentSchwingerBelongingWitnessRequired ≡ false
independentSchwingerWitnessPruned = refl
