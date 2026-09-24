{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact as R538
open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteProbabilityPositivityMachineChecked :
  R538.round538FiniteProbabilityPositivityCompilerLevel ≡ machineChecked
finiteProbabilityPositivityMachineChecked = refl

positiveProjectiveAssemblyMachineChecked :
  R538.round538PositiveProjectiveAssemblyCompilerLevel ≡ machineChecked
positiveProjectiveAssemblyMachineChecked = refl
