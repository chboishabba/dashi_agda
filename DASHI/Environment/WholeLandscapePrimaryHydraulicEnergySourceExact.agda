module DASHI.Environment.WholeLandscapePrimaryHydraulicEnergySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.WholeLandscapePrimaryDependencySourceRegistryExact as Sources

------------------------------------------------------------------------
-- PRIMARY FIELD SOURCE: LOW-PRESSURE DRIP HYDRAULIC ENERGY
--
-- Source result != electrical meter energy != lifecycle energy != DASHI
-- matched-service inference != recommendation.
------------------------------------------------------------------------

sokolLowPressureDrip2019 : Sources.PrimaryDependencySource
sokolLowPressureDrip2019 = Sources.primary-dependency-source
  "Julia Sokol; Susan Amrose; Vinay Nangia; Samer Talozi; Elizabeth Brownell; Gianni Montanaro; Khaled Abu Naser; Khalil Bany Mustafa; Abdeljabar Bahri; Bassou Bouazzama; Abdelaziz Bouizgaren; Naem Mazahrih; Rachid Moussadek; Lhassane Sikaoui; Amos G. Winter"
  "Energy Reduction and Uniformity of Low-Pressure Online Drip Irrigation Emitters in Field Tests"
  "Water 11(6):1195"
  2019
  "DOI 10.3390/w11061195"
  Sources.hydraulicHeadToWaterService
  Sources.hydraulicPerformanceExperiment
  "Field trials on farms in Morocco and Jordan compared low-pressure and conventional pressure-compensating emitters, measured water-distribution uniformity, pressure and flow, and reported lower hydraulic energy per delivered water volume for the low-pressure emitters under the tested systems."
  "Does not directly measure electrical input energy, does not establish pump/motor efficiency, lifecycle energy, universal gravity-service adequacy, crop benefit, or transport to arbitrary irrigation/aquaculture systems."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record HydraulicEnergySourceBoundary : Set where
  constructor hydraulic-energy-source-boundary
  field
    hydraulicEnergyAndElectricalEnergyRemainDistinct : Bool
    deliveredWaterVolumeAndAgronomicBenefitRemainDistinct : Bool
    primaryFieldResultAndDashiMatchedServiceRemainDistinct : Bool
    sourceOwnershipRemainsExternal : Bool
    lowerPressureAutomaticallyMeansLowerLifecycleEnergy : Bool

canonicalHydraulicEnergySourceBoundary : HydraulicEnergySourceBoundary
canonicalHydraulicEnergySourceBoundary =
  hydraulic-energy-source-boundary true true true true false

data HydraulicEnergyMeansElectricalEnergyPermission : Set where
data LowerPressureMeansLifecycleSavingPermission : Set where

hydraulicEnergyDoesNotEqualElectricalInputEnergy :
  HydraulicEnergyMeansElectricalEnergyPermission → ⊥
hydraulicEnergyDoesNotEqualElectricalInputEnergy ()

lowerPressureDoesNotProveLifecycleSaving :
  LowerPressureMeansLifecycleSavingPermission → ⊥
lowerPressureDoesNotProveLifecycleSaving ()
