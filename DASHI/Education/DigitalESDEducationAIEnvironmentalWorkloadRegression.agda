module DASHI.Education.DigitalESDEducationAIEnvironmentalWorkloadRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEducationAIEnvironmentalWorkloadExact as Workload
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

workshopNRegression : Workload.workshopStudentCount ≡ 49
workshopNRegression = refl

strongestPaidImplicationRegression :
  Workload.strongestPaidImplication ≡ Cone.restatesMeasuredResult
strongestPaidImplicationRegression = refl

preprintNotDeploymentLCARegression :
  Workload.PreprintWorkshopEstimateCreatesDeploymentLCA → ⊥
preprintNotDeploymentLCARegression = Workload.preprintWorkshopEstimateDoesNotCreateDeploymentLCA

energyEstimateNotLifecycleRegression :
  Workload.OperationalEnergyEstimateCreatesLifecycleFootprint → ⊥
energyEstimateNotLifecycleRegression = Workload.operationalEnergyEstimateDoesNotCreateLifecycleFootprint
