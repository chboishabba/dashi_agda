{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedLiteralConstructionRound483Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayRepresentedLiteralConstructionRound483Exact as R483
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R483.round483RepresentedLiteralConstructionCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

continuumNotIndependent :
  R483.continuumCarrierChosenIndependentlyFromRepresentedMeasure ≡ false
continuumNotIndependent = refl

schwingerNotIndependent :
  R483.schwingerChosenIndependentlyFromContinuumCarrier ≡ false
schwingerNotIndependent = refl
