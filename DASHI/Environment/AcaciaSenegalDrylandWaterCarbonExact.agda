module DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Wafa E. Abaker, Frank Berninger, Mike Starr,
-- "Changes in soil hydraulic properties, soil moisture and water balance in
-- Acacia senegal plantations of varying age in Sudan",
-- Journal of Arid Environments 150 (2018), 42--53.
-- DOI: 10.1016/j.jaridenv.2017.12.004
--
-- NEWS POINTER
-- Times of India Science Desk, 2026-09-16, summarising the 2018 study.
-- The journal article, not the news article, owns the scientific observations.
--
-- SOURCE BOUNDARY
-- The source investigates two Sudanese sites and reports plantation-age,
-- grassland-comparator, soil-carbon, soil-moisture and modelled water-balance
-- relationships.  The typed LES decomposition, consumer firewalls and
-- no-promotion theorems below are DASHI formalisation.
------------------------------------------------------------------------

primaryStudyDOI : String
primaryStudyDOI = "10.1016/j.jaridenv.2017.12.004"

record DrylandStudySource : Set where
  constructor dryland-study-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    geographicScope : String
    comparator : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open DrylandStudySource public

abakerBerningerStarr2018 : DrylandStudySource
abakerBerningerStarr2018 = dryland-study-source
  "Wafa E. Abaker; Frank Berninger; Mike Starr"
  "Changes in soil hydraulic properties, soil moisture and water balance in Acacia senegal plantations of varying age in Sudan"
  "Journal of Arid Environments 150:42-53"
  2018
  primaryStudyDOI
  "two sites in semi-arid Sudan; Acacia senegal plantations of varying age and adjacent grasslands"
  "adjacent grassland reference"
  "Plantation soil moisture increased with plantation age; SOC and plant-available water capacity also increased with age, while measured soil moisture remained higher in grasslands. The study's daily water-balance modelling produced lower runoff, greater infiltration and evapotranspiration, lower drainage and lower soil moisture in plantations relative to grasslands."
  "Does not establish that tree planting universally dries soil, that grassland universally dominates plantation, that SOC determines soil moisture, or that the study alone authorises a restoration intervention outside its studied systems."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Measurement / model-role separation.
--
-- This matters for LES because observed state and model-derived fluxes must not
-- silently become the same evidence type.  The paper reports TDR soil-moisture
-- measurements; hydraulic properties were computed with pedotransfer functions
-- based on texture and SOC; the daily water-balance model used SCS curve-number
-- runoff and crop-coefficient ET adjusted seasonally using NDVI.
------------------------------------------------------------------------

data EvidenceRole : Set where
  measured
  pedotransferComputed
  dailyBalanceModelled
  sourceInterpretation : EvidenceRole

record StudyCoordinate : Set where
  constructor study-coordinate
  field
    name : String
    role : EvidenceRole
    methodReference : String

open StudyCoordinate public

soilOrganicCarbonCoordinate : StudyCoordinate
soilOrganicCarbonCoordinate = study-coordinate
  "soil organic carbon"
  measured
  "source soil SOC observations used with soil texture as pedotransfer inputs"

soilMoistureCoordinate : StudyCoordinate
soilMoistureCoordinate = study-coordinate
  "soil moisture"
  measured
  "time-domain reflectometry (TDR) measurements during 2011-2012"

plantAvailableWaterCapacityCoordinate : StudyCoordinate
plantAvailableWaterCapacityCoordinate = study-coordinate
  "plant-available water capacity"
  pedotransferComputed
  "soil hydraulic properties computed from texture and SOC via pedotransfer functions"

runoffCoordinate : StudyCoordinate
runoffCoordinate = study-coordinate
  "Hortonian runoff"
  dailyBalanceModelled
  "simple daily water-balance model using the SCS runoff curve-number method"

infiltrationCoordinate : StudyCoordinate
infiltrationCoordinate = study-coordinate
  "infiltration"
  dailyBalanceModelled
  "water-balance consequence of rainfall minus modelled runoff"

evapotranspirationCoordinate : StudyCoordinate
evapotranspirationCoordinate = study-coordinate
  "evapotranspiration"
  dailyBalanceModelled
  "crop coefficients adjusted to seasonal values using NDVI"

drainageCoordinate : StudyCoordinate
drainageCoordinate = study-coordinate
  "drainage"
  dailyBalanceModelled
  "daily water-balance model output"

------------------------------------------------------------------------
-- Exact source-bounded qualitative pattern.
--
-- These Booleans encode only the direction-of-effect statements reported in
-- the paper/abstract.  They are not magnitudes, universal laws, or a substitute
-- for the paper's site-, age- and time-indexed data.
------------------------------------------------------------------------

record AcaciaStudyPattern : Set where
  constructor acacia-study-pattern
  field
    soilOrganicCarbonIncreasesWithPlantationAge : Bool
    plantAvailableWaterCapacityIncreasesWithPlantationAge : Bool
    plantationSoilMoistureIncreasesWithAge : Bool
    grasslandSoilMoistureHigherThanPlantations : Bool
    plantationRunoffLower : Bool
    plantationInfiltrationHigher : Bool
    plantationEvapotranspirationHigher : Bool
    plantationDrainageLower : Bool

open AcaciaStudyPattern public

canonicalStudyPattern : AcaciaStudyPattern
canonicalStudyPattern =
  acacia-study-pattern true true true true true true true true

------------------------------------------------------------------------
-- LES state decomposition.
--
-- Reuse the existing LES principle that a representation is only sufficient
-- relative to a task/consumer, and the existing SPAC principle that soil-water
-- availability, transpiration and carbon/biogeochemistry are separate coupled
-- coordinates.  This record is the study-specific observation surface only.
------------------------------------------------------------------------

record DrylandWaterCarbonState : Set where
  constructor dryland-water-carbon-state
  field
    siteIdentity : String
    landCover : String
    plantationAge : String
    soilOrganicCarbon : String
    soilTexture : String
    plantAvailableWaterCapacity : String
    measuredSoilMoisture : String
    runoff : String
    infiltration : String
    evapotranspiration : String
    drainage : String
    rainfallForcing : String
    observationWindow : String
    measurementProvenance : String
    modelProvenance : String

open DrylandWaterCarbonState public

record AcaciaLESWeld : Set where
  constructor acacia-les-weld
  field
    source : DrylandStudySource
    studyPattern : AcaciaStudyPattern
    taskRelativeCompressionOwner : String
    spacCouplingOwner : String
    soilCarbonConsumer : String
    retainedSoilMoistureConsumer : String
    infiltrationRunoffConsumer : String
    evapotranspirationConsumer : String
    drainageConsumer : String
    restorationDecisionConsumer : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    formalisationOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : formalisationOwner ≡ Attribution.dashiFormalisationOwner

open AcaciaLESWeld public

canonicalAcaciaLESWeld : AcaciaLESWeld
canonicalAcaciaLESWeld = acacia-les-weld
  abakerBerningerStarr2018
  canonicalStudyPattern
  "DASHI.Environment.LESResearchCrossPollinationExact.TaskFactorisation"
  "DASHI.Environment.SoilPlantAtmosphereContinuumExact"
  "soil organic carbon stock/content"
  "time-indexed retained soil moisture"
  "runoff/infiltration partition"
  "soil-plant-atmosphere evapotranspiration"
  "deep drainage flux"
  "multi-objective restoration/deployment decision"
  Attribution.externalSourceOwner refl
  Attribution.dashiFormalisationOwner refl

lesResearchBoundaryReused : LES.LESResearchCrossPollinationBoundary
lesResearchBoundaryReused = LES.canonicalLESResearchCrossPollinationBoundary

spacBoundaryReused : SPAC.SPACBoundary
spacBoundaryReused = SPAC.canonicalSPACBoundary

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
--
-- The study gives a particularly clean counterexample to single-coordinate
-- restoration reasoning: higher SOC / water-holding capacity can coexist with
-- lower realised soil moisture because flux partitioning and vegetation water
-- use remain active coordinates.
------------------------------------------------------------------------

data MoreSOCMeansMoreRealisedSoilMoisture : Set where
data HigherPAWCMeansHigherRealisedSoilMoisture : Set where
data MoreInfiltrationMeansHigherRetainedSoilMoisture : Set where
data LowerRunoffMeansHigherRetainedSoilMoisture : Set where
data MoreTreesMeansWetterSoil : Set where
data CarbonGainMeansHydrologicGain : Set where
data OneMetricMeansRestorationSuccess : Set where
data OneStudyMeansDeploymentAuthority : Set where

moreSOCDoesNotDefinitionallyMeanMoreRealisedSoilMoisture :
  MoreSOCMeansMoreRealisedSoilMoisture → ⊥
moreSOCDoesNotDefinitionallyMeanMoreRealisedSoilMoisture ()

higherPAWCDoesNotDefinitionallyMeanHigherRealisedSoilMoisture :
  HigherPAWCMeansHigherRealisedSoilMoisture → ⊥
higherPAWCDoesNotDefinitionallyMeanHigherRealisedSoilMoisture ()

moreInfiltrationDoesNotDefinitionallyMeanHigherRetainedSoilMoisture :
  MoreInfiltrationMeansHigherRetainedSoilMoisture → ⊥
moreInfiltrationDoesNotDefinitionallyMeanHigherRetainedSoilMoisture ()

lowerRunoffDoesNotDefinitionallyMeanHigherRetainedSoilMoisture :
  LowerRunoffMeansHigherRetainedSoilMoisture → ⊥
lowerRunoffDoesNotDefinitionallyMeanHigherRetainedSoilMoisture ()

moreTreesDoesNotDefinitionallyMeanWetterSoil : MoreTreesMeansWetterSoil → ⊥
moreTreesDoesNotDefinitionallyMeanWetterSoil ()

carbonGainDoesNotDefinitionallyMeanHydrologicGain : CarbonGainMeansHydrologicGain → ⊥
carbonGainDoesNotDefinitionallyMeanHydrologicGain ()

oneMetricDoesNotCreateRestorationSuccess : OneMetricMeansRestorationSuccess → ⊥
oneMetricDoesNotCreateRestorationSuccess ()

oneStudyDoesNotCreateDeploymentAuthority : OneStudyMeansDeploymentAuthority → ⊥
oneStudyDoesNotCreateDeploymentAuthority ()

------------------------------------------------------------------------
-- Explicit consumer and authority boundary.
------------------------------------------------------------------------

record AcaciaDrylandBoundary : Set where
  constructor acacia-dryland-boundary
  field
    soilCarbonAloneDeterminesSoilMoisture : Bool
    plantAvailableWaterCapacityAloneDeterminesRealisedMoisture : Bool
    infiltrationAloneDeterminesRetainedSoilMoisture : Bool
    runoffAloneDeterminesRetainedSoilMoisture : Bool
    moreTreeCoverAutomaticallyMeansWetterSoil : Bool
    carbonImprovementAutomaticallyMeansHydrologicImprovement : Bool
    singleMetricAutomaticallyRanksRestorationSuccess : Bool
    studyAutomaticallyGeneralisesBeyondStudiedSystems : Bool
    studyAutomaticallyAuthorisesDrylandTreePlanting : Bool
    measuredAndModelledCoordinatesCollapsed : Bool
    plantationAgeSiteAndComparatorMustRemainIndexed : Bool
    evapotranspirationMustRemainInWaterBalance : Bool
    taskRelativeConsumerSeparationReused : Bool
    soilPlantAtmosphereCouplingReused : Bool

open AcaciaDrylandBoundary public

canonicalAcaciaBoundary : AcaciaDrylandBoundary
canonicalAcaciaBoundary = acacia-dryland-boundary
  false false false false false false false false false false
  true true true true
