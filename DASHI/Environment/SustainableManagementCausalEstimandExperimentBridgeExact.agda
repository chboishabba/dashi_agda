module DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Environment.SustainableAgricultureManagementExact as Management
import DASHI.Environment.BerkeleyRapidThermophilicCompostingExact as Berkeley
import DASHI.Environment.PoultryBiologicalInterventionExact as Poultry
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- SUSTAINABLE MANAGEMENT -> CAUSAL ESTIMAND -> STATISTICAL REALISATION
--
-- Repository source-attribution boundary remains authoritative:
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != DASHI theorem != promotion/recommendation.
--
-- Current literature calibration used by downstream specialised owners:
--   Opazo, Salinas, Villasante (2025), Frontiers in Animal Science 6:1679614,
--   DOI 10.3389/fanim.2025.1679614: broiler probiotic meta-analysis with
--   substantial heterogeneity for Lactobacillus/mixed formulations.
--   de Toledo et al. (2020), PLoS ONE 15:e0232853,
--   DOI 10.1371/journal.pone.0232853: litter-treatment meta-analysis.
--   Sosnowka-Czajka et al. (2026), Animals 16:911,
--   DOI 10.3390/ani16060911: EM + zeolite litter treatment trial.
--   Syntropic farming overview (2025), Lancet Planetary Health,
--   DOI 10.1016/S2542-5196(25)00047-6: succession/stratification/pruning/mulch
--   literature review and explicit remaining evidence gaps.
--
-- This module does not import any empirical effect as a theorem.  It only
-- binds situated management intervention identity to the existing causal-
-- estimand and statistical-realisation owners.
------------------------------------------------------------------------

data InterventionFamily : Set where
  landManagementPractice
  rapidCompostProcess
  poultryBiologicalIntervention : InterventionFamily

record SituatedInterventionIdentity : Set where
  constructor situated-intervention-identity
  field
    family : InterventionFamily
    interventionReference : String
    siteHistoryReference : String
    implementationReference : String
    sourceAttributionReference : String

open SituatedInterventionIdentity public

record ManagementEstimandBinding : Set₂ where
  constructor management-estimand-binding
  field
    intervention : SituatedInterventionIdentity
    estimand : Estimand.CausalEffectEstimand
    interventionMatchesEstimandReference : String
    comparatorIsExplicit : Bool
    populationIsExplicit : Bool
    outcomeIsExplicit : Bool
    horizonIsExplicit : Bool
    siteHistoryRetained : Bool

open ManagementEstimandBinding public

record StatisticalManagementRealisation
    (binding : ManagementEstimandBinding) : Set₂ where
  constructor statistical-management-realisation
  field
    procedure : Statistical.EstimatorProcedure (estimand binding)
    realised : Statistical.RealisedEstimate procedure
    samplingDesignReference : String
    assignmentOrIdentificationReference : String
    measurementReference : String
    sourceDataProvenanceReference : String

open StatisticalManagementRealisation public

------------------------------------------------------------------------
-- Existing owner adapters.  These carry identity only; they do not claim that
-- the intervention paid an effect.
------------------------------------------------------------------------

managementPracticeIdentity :
  Management.ManagementPractice -> SituatedInterventionIdentity
managementPracticeIdentity practice =
  situated-intervention-identity
    landManagementPractice
    (Management.implementationReference practice)
    (Management.siteContext practice)
    (Management.timingContext practice)
    "DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact"

berkeleyBatchIdentity : Berkeley.CompostBatch -> SituatedInterventionIdentity
berkeleyBatchIdentity batch =
  situated-intervention-identity
    rapidCompostProcess
    (Berkeley.batchId batch)
    (Berkeley.siteContext batch)
    (Berkeley.temperatureTrajectoryReference batch)
    "Raabe rapid-compost lineage + batch-specific modern evidence receipts"

poultryInterventionIdentity :
  Poultry.BiologicalIntervention -> SituatedInterventionIdentity
poultryInterventionIdentity intervention =
  situated-intervention-identity
    poultryBiologicalIntervention
    (Poultry.organismOrStrain intervention)
    (Poultry.housingContext intervention)
    (Poultry.timingAndDuration intervention)
    (Poultry.provenanceReference intervention)

------------------------------------------------------------------------
-- LES same-practice context retention.
------------------------------------------------------------------------

record LESExperimentContext : Set where
  constructor les-experiment-context
  field
    before : LES.SituatedObservation
    after : LES.SituatedObservation
    managementIdentity : SituatedInterventionIdentity
    comparatorReference : String
    assignmentReference : String
    outcomeMeasurementReference : String

open LESExperimentContext public

------------------------------------------------------------------------
-- No-shortcut / WrongType barriers.
------------------------------------------------------------------------

data SameTechniqueMeansSameInterventionPermission : Set where
data SameInterventionMeansSameEffectPermission : Set where
data SameOutcomeMeansSameMechanismPermission : Set where
data ObservedDifferenceMeansCausalEffectPermission : Set where
data MetaAnalysisMeansSiteRecommendationPermission : Set where
data FeedProbioticMeansLitterTreatmentPermission : Set where
data HotCompostMeansMatureCompostPermission : Set where
data SyntropicLabelMeansSoilCarbonGainPermission : Set where
data EstimateMeansPortableEffectPermission : Set where

sameTechniqueDoesNotEraseImplementation : SameTechniqueMeansSameInterventionPermission -> ⊥
sameTechniqueDoesNotEraseImplementation ()

sameInterventionDoesNotDetermineEffect : SameInterventionMeansSameEffectPermission -> ⊥
sameInterventionDoesNotDetermineEffect ()

sameOutcomeDoesNotIdentifyMechanism : SameOutcomeMeansSameMechanismPermission -> ⊥
sameOutcomeDoesNotIdentifyMechanism ()

observedDifferenceDoesNotIdentifyCause : ObservedDifferenceMeansCausalEffectPermission -> ⊥
observedDifferenceDoesNotIdentifyCause ()

metaAnalysisDoesNotByItselfPromoteSiteRecommendation : MetaAnalysisMeansSiteRecommendationPermission -> ⊥
metaAnalysisDoesNotByItselfPromoteSiteRecommendation ()

feedProbioticEvidenceDoesNotBecomeLitterEvidence : FeedProbioticMeansLitterTreatmentPermission -> ⊥
feedProbioticEvidenceDoesNotBecomeLitterEvidence ()

hotProcessDoesNotDefinitionallyMeanMatureProduct : HotCompostMeansMatureCompostPermission -> ⊥
hotProcessDoesNotDefinitionallyMeanMatureProduct ()

syntropicIdentityDoesNotProveSoilCarbonGain : SyntropicLabelMeansSoilCarbonGainPermission -> ⊥
syntropicIdentityDoesNotProveSoilCarbonGain ()

estimatedEffectDoesNotAutomaticallyTransport : EstimateMeansPortableEffectPermission -> ⊥
estimatedEffectDoesNotAutomaticallyTransport ()

record SustainableManagementCausalBoundary : Set where
  constructor sustainable-management-causal-boundary
  field
    interventionPopulationComparatorOutcomeTimeAreExplicit : Bool
    implementationAndSiteHistoryRemainFirstClass : Bool
    attributionAndCausalIdentificationRemainDistinct : Bool
    estimatorAndEstimandRemainDistinct : Bool
    statisticalEstimateAndRecommendationRemainDistinct : Bool
    routeSpecificPoultryEvidenceRetained : Bool
    compostProcessAndProductMaturityRemainDistinct : Bool
    managementLabelAutomaticallyIdentifiesEffect : Bool

canonicalSustainableManagementCausalBoundary : SustainableManagementCausalBoundary
canonicalSustainableManagementCausalBoundary =
  sustainable-management-causal-boundary
    true true true true true true true false
