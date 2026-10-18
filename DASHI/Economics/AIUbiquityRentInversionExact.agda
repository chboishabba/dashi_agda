module DASHI.Economics.AIUbiquityRentInversionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal

------------------------------------------------------------------------
-- AI UBIQUITY / RENT INVERSION
--
-- Social or technical usefulness is kept distinct from producer rent.
-- Datacentre buildout proves committed capital, not terminal external demand.
-- Open weights, small reasoning controllers, local inference and distributed
-- execution may increase total use while reducing proprietary rent per unit.
------------------------------------------------------------------------

data InferenceLocation : Set where
  onDevice : InferenceLocation
  localEdge : InferenceLocation
  siteCluster : InferenceLocation
  remoteCloud : InferenceLocation

record DeploymentRegime : Set where
  constructor deploymentRegime
  field
    massAdoption : Bool
    openWeightSubstitutability : Bool
    smallControllerAdequacy : Bool
    toolAndWebAugmentation : Bool
    localInferenceFeasible : Bool
    distributedInferenceFeasible : Bool
    remoteCloudRequiredForSafetyLoop : Bool
    proprietaryScarcityRentProtected : Bool

open DeploymentRegime public

localCommoditisationRegime : DeploymentRegime → Bool
localCommoditisationRegime r =
  massAdoption r
  ∧ openWeightSubstitutability r
  ∧ smallControllerAdequacy r
  ∧ toolAndWebAugmentation r
  ∧ localInferenceFeasible r

record RoboticsLatencyBoundary : Set where
  constructor roboticsLatencyBoundary
  field
    safetyReflexLocation : InferenceLocation
    perceptionPlanningLocation : InferenceLocation
    fleetLearningLocation : InferenceLocation
    safetyCriticalLoopRequiresBoundedLocalLatency : Bool
    cloudMayStillServeNonCriticalWork : Bool

open RoboticsLatencyBoundary public

canonicalRoboticsLatencyBoundary : RoboticsLatencyBoundary
canonicalRoboticsLatencyBoundary =
  roboticsLatencyBoundary
    onDevice
    localEdge
    remoteCloud
    true
    true

data SocialValueImpliesProducerRentPermission : Set where
data DatacentreBuildoutImpliesTerminalDemandPermission : Set where
data MassAdoptionImpliesCloudRentPermission : Set where
data OpenWeightsImplyZeroCloudValuePermission : Set where

socialValueDoesNotAutoCloseProducerRent :
  SocialValueImpliesProducerRentPermission → ⊥
socialValueDoesNotAutoCloseProducerRent ()

buildoutDoesNotAutoCloseTerminalDemand :
  DatacentreBuildoutImpliesTerminalDemandPermission → ⊥
buildoutDoesNotAutoCloseTerminalDemand ()

massAdoptionDoesNotAutoCloseCloudRent :
  MassAdoptionImpliesCloudRentPermission → ⊥
massAdoptionDoesNotAutoCloseCloudRent ()

openWeightsDoNotAutoEraseCloudValue :
  OpenWeightsImplyZeroCloudValuePermission → ⊥
openWeightsDoNotAutoEraseCloudValue ()

record UbiquityRentInversionWitness : Set where
  constructor ubiquityRentInversionWitness
  field
    regime : DeploymentRegime
    commoditisationObserved : localCommoditisationRegime regime ≡ true
    proprietaryRentPerUnitFalls : Bool
    totalAIUseRises : Bool
    socialUtilityMayRise : Bool
    sunkFrontierCapitalRecoveryMayWorsen : Bool

open UbiquityRentInversionWitness public

record InfrastructureDemandBoundary : Set where
  constructor infrastructureDemandBoundary
  field
    datacentreCapacityCommitted : Bool
    independentTerminalPayerEstablished : Bool
    buildoutAloneCountsAsTerminalValidation : Bool
    buildoutAloneCountsAsTerminalValidationIsFalse :
      buildoutAloneCountsAsTerminalValidation ≡ false

canonicalInfrastructureDemandBoundary : InfrastructureDemandBoundary
canonicalInfrastructureDemandBoundary =
  infrastructureDemandBoundary true false false refl

record TechnologySuccessCapitalLossBoundary : Set where
  constructor technologySuccessCapitalLossBoundary
  field
    technologyCapabilityImproves : Bool
    inferenceUnitCostFalls : Bool
    substitutabilityRises : Bool
    proprietaryRentFalls : Bool
    capitalRecoveryAutomaticallyImproves : Bool
    capitalRecoveryAutomaticallyImprovesIsFalse :
      capitalRecoveryAutomaticallyImproves ≡ false

canonicalTechnologySuccessCapitalLossBoundary :
  TechnologySuccessCapitalLossBoundary
canonicalTechnologySuccessCapitalLossBoundary =
  technologySuccessCapitalLossBoundary
    true true true true false refl

terminalValidationStillRequired : String
terminalValidationStillRequired =
  "AI technological success, high utilisation and datacentre construction remain distinct from terminal external cash-flow validation."
