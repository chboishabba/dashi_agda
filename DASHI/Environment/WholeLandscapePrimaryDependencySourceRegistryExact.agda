module DASHI.Environment.WholeLandscapePrimaryDependencySourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PRIMARY-SOURCE REGISTRY FOR WHOLE-LANDSCAPE DEPENDENCY PAYMENTS
--
-- Attribution invariant:
-- primary source result != DASHI dependency weld != causal generalisation
-- != transport != recommendation.
--
-- These source objects only license the bounded readings written below.
------------------------------------------------------------------------

data PrimaryDependencyDomain : Set where
  grazingToFuel
  nitrogenToCropSoil
  hydraulicHeadToWaterService : PrimaryDependencyDomain

data PrimaryEvidenceDesign : Set where
  replicatedFactorialFieldExperiment
  isotopeTracerFieldExperiment
  hydraulicPerformanceExperiment : PrimaryEvidenceDesign

record PrimaryDependencySource : Set where
  constructor primary-dependency-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    domain : PrimaryDependencyDomain
    design : PrimaryEvidenceDesign
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PrimaryDependencySource public

targetedCattleFuel2024 : PrimaryDependencySource
targetedCattleFuel2024 = primary-dependency-source
  "Christopher L. Schachtschneider; Eva K. Strand; Karen L. Launchbaugh; Scott Jensen"
  "Targeted Cattle Grazing to Alter Fuels and Reduce Fire Behavior Metrics in Shrub-Grasslands"
  "Rangeland Ecology & Management 96:105-116"
  2024
  "DOI 10.1016/j.rama.2024.05.010"
  grazingToFuel
  replicatedFactorialFieldExperiment
  "In two big-sagebrush communities, replicated cattle-grazing treatments altered herbaceous fuel load/height and measured fire-behaviour metrics; the fire-behaviour reduction reported by the study was bounded by shrub-cover conditions."
  "Does not establish a universal grazing-to-wildfire-risk theorem, does not identify patch-burn grazing with cultural burning, and does not transport the result to other herbivores, fuels, climates or shrub structure without new receipts."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

wheat15N2025 : PrimaryDependencySource
wheat15N2025 = primary-dependency-source
  "Aixia Xu; Khuram Shehzad Khan; Xuexue Wei; Yafei Chen; Yixun Zhou; Chongrui Sun; Zechariah Effah; Lingling Li"
  "Fertilizer nitrogen use efficiency and its fate in the spring wheat-soil system under varying N-fertilizer rates: A two-year field study using 15N tracer"
  "Soil & Tillage Research 252:106612"
  2025
  "DOI 10.1016/j.still.2025.106612"
  nitrogenToCropSoil
  isotopeTracerFieldExperiment
  "Two on-farm 15N tracer experiments partitioned fertilizer-derived nitrogen among crop uptake, soil residual and loss under multiple N rates, demonstrating that delivered fertilizer N and crop uptake are distinct measured coordinates."
  "Does not establish the same partition for PAW, compost, BNF, aquaponic recycling, KNF, other crops, other soils or other climates; it does not make fertilizer N equivalent to plant-available or plant-uptaken N by label."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

gravityDripHead2024 : PrimaryDependencySource
gravityDripHead2024 = primary-dependency-source
  "G. T. Patle"
  "Evaluation of a gravity-fed drip irrigation system under varying hydraulic head and land slope for hilly terrain"
  "Agricultural Engineering International: CIGR Journal 26(3)"
  2024
  "CIGR article 9117; published 2024-09-27"
  hydraulicHeadToWaterService
  hydraulicPerformanceExperiment
  "The experiment varied hydraulic head and field slope in a gravity-fed drip system and directly measured coefficient/emission uniformity; performance changed with head and slope under the reported geometry."
  "Does not establish universal pump displacement, lifecycle energy saving, crop response, aquaculture service, or adequacy of an arbitrary gravity-fed system; exact head, flow, losses and service still require measurement."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

canonicalWholeLandscapePrimarySources : List PrimaryDependencySource
canonicalWholeLandscapePrimarySources =
  targetedCattleFuel2024 ∷ wheat15N2025 ∷ gravityDripHead2024 ∷ []

------------------------------------------------------------------------
-- Non-laundering barriers.
------------------------------------------------------------------------

data PrimaryStudyMeansUniversalDependencyPermission : Set where
data PrimaryStudyMeansRecommendationPermission : Set where
data FireBehaviorMetricMeansWildfireRiskPermission : Set where
data FertilizerNMeansPlantUptakePermission : Set where
data HydraulicHeadMeansDeliveredServicePermission : Set where

primaryStudyDoesNotMeanUniversalDependency :
  PrimaryStudyMeansUniversalDependencyPermission → ⊥
primaryStudyDoesNotMeanUniversalDependency ()

primaryStudyDoesNotMeanRecommendation :
  PrimaryStudyMeansRecommendationPermission → ⊥
primaryStudyDoesNotMeanRecommendation ()

fireBehaviorMetricDoesNotEqualWildfireRisk :
  FireBehaviorMetricMeansWildfireRiskPermission → ⊥
fireBehaviorMetricDoesNotEqualWildfireRisk ()

fertilizerNitrogenDoesNotEqualPlantUptake :
  FertilizerNMeansPlantUptakePermission → ⊥
fertilizerNitrogenDoesNotEqualPlantUptake ()

hydraulicHeadDoesNotEqualDeliveredService :
  HydraulicHeadMeansDeliveredServicePermission → ⊥
hydraulicHeadDoesNotEqualDeliveredService ()

record PrimaryDependencyAttributionBoundary : Set where
  constructor primary-dependency-attribution-boundary
  field
    sourceResultAndDashiDependencyRemainDistinct : Bool
    sourceResultAndTransportRemainDistinct : Bool
    sourceResultAndRecommendationRemainDistinct : Bool
    primarySourceOwnershipRemainsExternal : Bool
    dashiCrossSourceWeldMustRemainDashiOwned : Bool
    sourceResultAutomaticallyPaysUniversalDependency : Bool

canonicalPrimaryDependencyAttributionBoundary : PrimaryDependencyAttributionBoundary
canonicalPrimaryDependencyAttributionBoundary =
  primary-dependency-attribution-boundary true true true true true false
