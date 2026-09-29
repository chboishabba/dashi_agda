{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5RepresentedOS05Round455Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5RepresentedOS05Round455Exact as R455
open import DASHI.Physics.YangMills.CompactLieProofLevel

representedOS05TransportMachineChecked :
  R455.round455RepresentedOS05TransportCompilerLevel ≡ machineChecked
representedOS05TransportMachineChecked = refl

noNewPhysicalMomentEstimate :
  R455.round455NewPhysicalMomentEstimateRequired ≡ false
noNewPhysicalMomentEstimate = refl

wholeMeasureEqualityPruned :
  R455.round455WholeMeasureEqualityRequired ≡ false
wholeMeasureEqualityPruned = refl
