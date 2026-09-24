{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as R514
open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteMomentRegularityCompilerMachineChecked :
  R514.round514FiniteMomentRegularityCompilerLevel ≡ machineChecked
finiteMomentRegularityCompilerMachineChecked = refl

finiteGrowthCompilerMachineChecked :
  R514.round514FiniteExponentialGrowthCompilerLevel ≡ machineChecked
finiteGrowthCompilerMachineChecked = refl

noAdditionalFiniteRegularityEstimate :
  R514.literalRound514AdditionalFiniteRegularityEstimateLevel ≡ machineChecked
noAdditionalFiniteRegularityEstimate = refl

noAdditionalFiniteGrowthEstimate :
  R514.literalRound514AdditionalFiniteGrowthEstimateLevel ≡ machineChecked
noAdditionalFiniteGrowthEstimate = refl
