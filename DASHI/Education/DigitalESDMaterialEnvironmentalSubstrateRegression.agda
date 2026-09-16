module DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material

lifecycleStageCountRegression : Material.digitalMaterialStageCount ≡ 8
lifecycleStageCountRegression = refl

substrateQuestionCountRegression : Material.materialAuditQuestionCount ≡ 10
substrateQuestionCountRegression = refl

aiLabelNotFootprintRegression : Material.AILabelCreatesDeploymentFootprint → ⊥
aiLabelNotFootprintRegression = Material.aiLabelDoesNotCreateDeploymentFootprint

computerCountNotSustainabilityRegression : Material.DeviceCountCreatesEnvironmentalSustainability → ⊥
computerCountNotSustainabilityRegression = Material.deviceCountDoesNotCreateEnvironmentalSustainability
