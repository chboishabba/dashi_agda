{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Exact as R576
open import DASHI.Physics.YangMills.CompactLieProofLevel

wextCompilerMachineChecked :
  R576.round576PreferredWEXTCompilerLevel ≡ machineChecked
wextCompilerMachineChecked = refl

noMagnitudeCalibrationPhysicalLeaf :
  R576.round576MagnitudeCalibrationPhysicalInputRequired ≡ false
noMagnitudeCalibrationPhysicalLeaf = refl

continuityStillStandardImported :
  R576.round576RationalMagnitudeContinuityLevel ≡ standardImported
continuityStillStandardImported = refl
