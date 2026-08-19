module DASHI.Education.EarlyLearningCounterfactualQualityRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Education.EarlyLearningComparativeArchitectureExact as Architecture
import DASHI.Education.EarlyLearningCounterfactualHeterogeneityExact as Counterfactual
import DASHI.Education.EarlyLearningEntitlementRouteSeparationExact as Entitlement
import DASHI.Education.EarlyLearningEvidenceRevisionHorizonExact as Horizon
import DASHI.Education.EarlyLearningMultiOutcomeVectorExact as Outcomes
import DASHI.Education.EarlyLearningQualityWorkforceLoadBearingExact as Quality
import DASHI.Education.EarlyLearningSituatedPolicyRoutingSafetyExact as Routing
import DASHI.Education.EarlyLearningTakeupStratificationExact as Takeup

------------------------------------------------------------------------
-- Focused source/API regression for the comparative causal/evaluation tranche.
------------------------------------------------------------------------

interventionLabelRegression :
  Intersection.FactorsThrough
    Counterfactual.interventionProjection
    Counterfactual.counterfactualRelativeEffect → ⊥
interventionLabelRegression = Counterfactual.interventionLabelCannotDetermineEffect

subgroupRoutingRegression :
  Intersection.FactorsThrough
    Counterfactual.observedGroupProjection Counterfactual.withinGroupEffect → ⊥
subgroupRoutingRegression = Counterfactual.observedGroupCannotDetermineIndividualEffect

professionalFloorRegression :
  Intersection.FactorsThrough
    Architecture.professionalFloorProjection Architecture.comparativeOutcomeWitness → ⊥
professionalFloorRegression = Architecture.professionalFloorCannotDetermineOutcome

labourChildAxisRegression :
  Intersection.FactorsThrough
    Outcomes.labourMatchedProjection Outcomes.childSignalAt → ⊥
labourChildAxisRegression = Outcomes.labourGainCannotDetermineChildEffect

childFiscalAxisRegression :
  Intersection.FactorsThrough
    Outcomes.sameChildProjection Outcomes.fiscalSignalAt → ⊥
childFiscalAxisRegression = Outcomes.childSignalCannotDetermineFiscalEffect

professionalQualityRegression :
  Intersection.FactorsThrough
    Quality.professionalRelationProjection Quality.qualityProjection → ⊥
professionalQualityRegression = Quality.professionalPresenceCannotDetermineQuality

entitlementRolloutRegression :
  Intersection.FactorsThrough
    Quality.entitlementProjection Quality.rolloutProjection → ⊥
entitlementRolloutRegression = Quality.universalEntitlementCannotDetermineRolloutCapacity

entitlementRouteRegression :
  Intersection.FactorsThrough
    Entitlement.universalEntitlement Entitlement.parallelFamilyRoute → ⊥
entitlementRouteRegression = Entitlement.universalEntitlementCannotDetermineDeliveryRoute

parallelRouteFloorRegression :
  Intersection.FactorsThrough
    Entitlement.parallelFamilyRoute Entitlement.professionalFloor → ⊥
parallelRouteFloorRegression = Entitlement.parallelFamilyOptionCannotDetermineProfessionalFloor

availabilityUptakeRegression :
  Intersection.FactorsThrough Takeup.availabilityProjection Takeup.uptakeAt → ⊥
availabilityUptakeRegression = Takeup.availabilityCannotDetermineUptake

availabilityLabourRegression :
  Intersection.FactorsThrough
    Takeup.availabilityProjection Takeup.labourIncidenceAt → ⊥
availabilityLabourRegression = Takeup.availabilityCannotDetermineLabourIncidence

vintageSignalRegression :
  Intersection.FactorsThrough Horizon.updatedVintageProjection Horizon.updatedSignalAt → ⊥
vintageSignalRegression = Horizon.vintageAloneCannotDetermineEvidenceSignal

measurementHorizonRegression :
  Intersection.FactorsThrough Horizon.horizonProjection Horizon.horizonSignal → ⊥
measurementHorizonRegression = Horizon.measurementHorizonCannotDetermineOutcomeDirection

coarsePolicyRoutingRegression :
  Policy.PolicyRelativeSafety
    Routing.supportSystem
    Routing.entitlementRouteFitObservation
    Routing.coarseEntitlementPolicy → ⊥
coarsePolicyRoutingRegression =
  Routing.coarseEntitlementPolicyCannotCarrySituatedRoutingSafety
