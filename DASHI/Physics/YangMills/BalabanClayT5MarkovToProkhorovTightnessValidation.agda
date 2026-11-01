{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkovToProkhorovTightnessValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5MarkovToProkhorovTightnessExact as Bridge

selectedMarkovContainmentProducesUniformTightness :
  Bridge.selectedMarkovToUniformTightnessCompilerLevel ≡ machineChecked
selectedMarkovContainmentProducesUniformTightness = refl

uniformTightnessProducesSelectedProkhorovInput :
  Bridge.selectedUniformTightnessToProkhorovInputCompilerLevel ≡ machineChecked
uniformTightnessProducesSelectedProkhorovInput = refl

selectedMarkovRouteReachesProkhorovExtraction :
  Bridge.selectedMarkovToProkhorovExtractionCompilerLevel ≡ machineChecked
selectedMarkovRouteReachesProkhorovExtraction = refl

prokhorovIsStandardAuthority :
  Bridge.prokhorovAuthorityLevel ≡ standardImported
prokhorovIsStandardAuthority = refl

expectationIntegralSemanticsRemainPhysical :
  Bridge.selectedExpectationProbabilityIntegralSemanticsLevel ≡ conditional
expectationIntegralSemanticsRemainPhysical = refl

coerciveGeometryRemainsPhysical :
  Bridge.selectedCoerciveObservableGeometryLevel ≡ conditional
coerciveGeometryRemainsPhysical = refl

compactSublevelGeometryRemainsPhysical :
  Bridge.selectedCompactSublevelGeometryLevel ≡ conditional
compactSublevelGeometryRemainsPhysical = refl
