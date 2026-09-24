{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedOS05Round481Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayRepresentedOS05Round481Exact as R481
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R481.round481RepresentedOS05CompilerLevel ≡ machineChecked
compilerMachineChecked = refl

noNewMomentEstimate :
  R481.newMomentEstimateRequired ≡ false
noNewMomentEstimate = refl

noWholeMeasureEquality :
  R481.wholeMeasureRecordEqualityRequired ≡ false
noWholeMeasureEquality = refl
