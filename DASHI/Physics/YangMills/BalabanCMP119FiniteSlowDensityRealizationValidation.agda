module DASHI.Physics.YangMills.BalabanCMP119FiniteSlowDensityRealizationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FiniteSlowDensityRealizationExact as Density

compilerClosed :
  Density.cmp119FiniteSlowDensityCompilerLevel ≡ machineChecked
compilerClosed = refl

weightFunctionRemainsPhysical :
  Density.cmp119SelectedDensityWeightFunctionLevel ≡ conditional
weightFunctionRemainsPhysical = refl

nonnegativityRemainsPhysical :
  Density.cmp119SelectedDensityWeightNonnegativeLevel ≡ conditional
nonnegativityRemainsPhysical = refl

positiveWitnessRemainsPhysical :
  Density.cmp119SelectedDensityPositiveWitnessLevel ≡ conditional
positiveWitnessRemainsPhysical = refl
