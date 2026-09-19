{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4MarkovProkhorovValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5Path4MarkovProkhorovExact as Path4

path4GaugeEnergyProducesUniformTightness :
  Path4.path4GaugeEnergyToUniformTightnessCompilerLevel ≡ machineChecked
path4GaugeEnergyProducesUniformTightness = refl

path4UniformTightnessProducesProkhorovInput :
  Path4.path4UniformTightnessToProkhorovCompilerLevel ≡ machineChecked
path4UniformTightnessProducesProkhorovInput = refl

path4NonnegativeCoerciveGeometryReused :
  Path4.path4GaugeEnergyNonnegativeAndCoerciveLevel ≡ machineChecked
path4NonnegativeCoerciveGeometryReused = refl

path4ExpectationIntegralSemanticsRemainPhysical :
  Path4.path4SelectedExpectationProbabilityIntegralSemanticsLevel ≡ conditional
path4ExpectationIntegralSemanticsRemainPhysical = refl

path4CompactSublevelAdmissibilityRemainsPhysical :
  Path4.path4CompactSublevelAdmissibilityLevel ≡ conditional
path4CompactSublevelAdmissibilityRemainsPhysical = refl
