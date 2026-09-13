module DASHI.Environment.PoultryBiologicalInterventionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.EcologicalEvidenceGates as Evidence

------------------------------------------------------------------------
-- POULTRY BIOLOGICAL / MICROBIAL INTERVENTION SURFACE
--
-- Current evidence calibration:
--   Opazo, Salinas, Villasante (2025), Frontiers in Animal Science 6:1679614,
--   DOI 10.3389/fanim.2025.1679614: systematic review/meta-analysis of broiler
--   probiotic formulations. Dietary Lactobacillus groups showed pooled BWG/FCR
--   effects but substantial heterogeneity.
--
--   Jha et al. (2020), systematic review of direct-fed microbials/probiotics in
--   poultry, PMID 33066185 / PMCID PMC7602066: effects and context dependence.
--
--   Systematic review/meta-analysis of litter treatments, PMID 32374780, and
--   litter-management NMA DOI 10.1017/S1466252319000227: environmental litter
--   treatments are a separate evidence family from feed probiotics.
--
-- SOURCE BOUNDARY
-- "Lactobacillus for chickens" is not one intervention. Strain/formulation,
-- route, dose/viability, flock/housing/litter context and target outcome are
-- first-class. In particular, dietary probiotic evidence is not silently
-- transferred to spraying or inoculating litter/coop surfaces.
------------------------------------------------------------------------

data BiologicalAgentClass : Set where
  lactobacillaceae
  bacillusGroup
  yeastGroup
  mixedProbiotic
  definedLacticAcidBacteria
  undefinedMicrobialConsortium : BiologicalAgentClass

data AdministrationRoute : Set where
  feedRoute
  drinkingWaterRoute
  gavageRoute
  respiratoryOrNasalRoute
  litterOrBeddingInoculation
  environmentalSurfaceApplication
  fermentedFeedRoute
  manureOrCompostTreatment : AdministrationRoute

data PoultryOutcome : Set where
  bodyWeightGain
  feedConversionRatio
  gutMicrobiome
  pathogenCarriage
  immuneOrBarrierResponse
  litterPH
  litterMoisture
  litterMicrobiome
  ammoniaConcentration
  ammoniaEmission
  odourOrVOC
  mortality
  footpadOrWelfare
  manureNitrogenRetention
  antimicrobialUse
  antimicrobialResistance : PoultryOutcome

data PoultryEvidenceState : Set where
  practiceDescription
  inVitroEvidence
  controlledBirdTrial
  flockFieldTrial
  systematicReview
  metaAnalysis
  causalEstimate
  recommendationAdmitted : PoultryEvidenceState

record BiologicalIntervention : Set where
  constructor biological-intervention
  field
    sourceStage : Sources.ClaimStage
    agentClass : BiologicalAgentClass
    organismOrStrain : String
    formulation : String
    route : AdministrationRoute
    doseOrConcentration : String
    viabilityOrQualityReference : String
    timingAndDuration : String
    flockStage : String
    housingContext : String
    litterOrSubstrateContext : String
    ventilationReference : String
    provenanceReference : String

open BiologicalIntervention public

record PoultryOutcomeEvidence : Set where
  constructor poultry-outcome-evidence
  field
    intervention : BiologicalIntervention
    outcome : PoultryOutcome
    evidenceState : PoultryEvidenceState
    comparator : String
    measurementMethod : String
    resultReference : String
    uncertaintyOrHeterogeneityReference : String
    geographicAndProductionScope : String

open PoultryOutcomeEvidence public

------------------------------------------------------------------------
-- Canonical route-separated examples.
------------------------------------------------------------------------

dietaryLactobacillusCandidate : BiologicalIntervention
dietaryLactobacillusCandidate = biological-intervention
  Sources.externalSourceClaim
  lactobacillaceae
  "strain-specific identity required; genus-level meta-analysis is not a strain receipt"
  "single or mixed probiotic formulation"
  feedRoute
  "CFU/kg or equivalent study-specific dose"
  "viability and product-quality evidence required"
  "trial-specific"
  "broiler growth stage explicit"
  "housing system explicit"
  "litter substrate recorded but not the administration route"
  "ventilation recorded as environmental modifier"
  "Opazo et al. 2025 DOI 10.3389/fanim.2025.1679614; Jha et al. 2020 PMID 33066185"

litterLacticAcidBacteriaCandidate : BiologicalIntervention
litterLacticAcidBacteriaCandidate = biological-intervention
  Sources.dashiReconstruction
  definedLacticAcidBacteria
  "exact strain or consortium required"
  "environmental biological amendment"
  litterOrBeddingInoculation
  "CFU per litter mass/area or equivalent must be supplied"
  "viability and batch provenance required"
  "application and reapplication schedule explicit"
  "flock stage explicit"
  "coop/broiler-house context explicit"
  "litter material, reuse history, moisture and depth explicit"
  "ventilation rate/context explicit"
  "candidate intervention class; litter-treatment evidence must be route-specific and does not descend from dietary probiotic evidence"

------------------------------------------------------------------------
-- Source/provenance and safety gates.
------------------------------------------------------------------------

record PoultryMicrobialAdmission : Set where
  constructor poultry-microbial-admission
  field
    intervention : BiologicalIntervention
    inoculantProvenance : Evidence.InoculantProvenanceWitness
    pathogenRisk : Evidence.PathogenRiskWitness
    regulatoryReference : String
    animalSafetyReference : String
    workerExposureReference : String
    environmentalReleaseReference : String

open PoultryMicrobialAdmission public

------------------------------------------------------------------------
-- Causal estimand interface.  This is intentionally consumer-indexed and can
-- be welded to the repository causal/statistical realization owner without
-- treating a literature association as an identified effect.
------------------------------------------------------------------------

record PoultryInterventionEstimand : Set where
  constructor poultry-intervention-estimand
  field
    treatment : BiologicalIntervention
    comparator : String
    targetPopulation : String
    outcome : PoultryOutcome
    timeHorizon : String
    siteHistoryFibre : String
    assignmentOrIdentificationReference : String
    statisticalRealizationReference : String

open PoultryInterventionEstimand public

record PoultryRecommendationReceipt : Set where
  constructor poultry-recommendation-receipt
  field
    estimand : PoultryInterventionEstimand
    effectEvidenceReference : String
    transferEvidenceReference : String
    biosecurityReference : String
    safetyReference : String
    regulatoryReference : String
    resourceCostReference : String
    decisionObjectiveReference : String

open PoultryRecommendationReceipt public

------------------------------------------------------------------------
-- WrongType / non-promotion barriers.
------------------------------------------------------------------------

data GenusMeansStrainEfficacyPermission : Set where
data InVitroMeansInVivoPermission : Set where
data FeedMeansLitterPermission : Set where
data LowerPHMeansLowerAmmoniaPermission : Set where
data NaturalMeansSafePermission : Set where
data OneFlockMeansPortablePermission : Set where
data ProbioticMeansColonisationPermission : Set where
data OdourMeansAmmoniaPermission : Set where
data PathogenReductionMeansEliminationPermission : Set where
data DietaryEvidenceMeansCoopSprayEvidencePermission : Set where

genusDoesNotProveStrainEfficacy : GenusMeansStrainEfficacyPermission → ⊥
genusDoesNotProveStrainEfficacy ()

inVitroDoesNotProveInVivo : InVitroMeansInVivoPermission → ⊥
inVitroDoesNotProveInVivo ()

feedInterventionIsNotLitterIntervention : FeedMeansLitterPermission → ⊥
feedInterventionIsNotLitterIntervention ()

lowerLitterPHDoesNotUniversallyProveLowerAmmonia : LowerPHMeansLowerAmmoniaPermission → ⊥
lowerLitterPHDoesNotUniversallyProveLowerAmmonia ()

naturalDoesNotProveSafeOrAuthorized : NaturalMeansSafePermission → ⊥
naturalDoesNotProveSafeOrAuthorized ()

oneFlockDoesNotProvePortability : OneFlockMeansPortablePermission → ⊥
oneFlockDoesNotProvePortability ()

probioticAdministrationDoesNotProvePermanentColonisation : ProbioticMeansColonisationPermission → ⊥
probioticAdministrationDoesNotProvePermanentColonisation ()

odourReductionDoesNotEqualAmmoniaReduction : OdourMeansAmmoniaPermission → ⊥
odourReductionDoesNotEqualAmmoniaReduction ()

pathogenReductionDoesNotMeanElimination : PathogenReductionMeansEliminationPermission → ⊥
pathogenReductionDoesNotMeanElimination ()

dietaryEvidenceDoesNotTransferToCoopSpray : DietaryEvidenceMeansCoopSprayEvidencePermission → ⊥
dietaryEvidenceDoesNotTransferToCoopSpray ()

record PoultryBiologicalInterventionBoundary : Set where
  constructor poultry-biological-intervention-boundary
  field
    strainAndRouteAreFirstClass : Bool
    feedAndLitterEvidenceRemainDistinct : Bool
    housingAndVentilationAreContextCoordinates : Bool
    environmentalInoculationNeedsOwnEvidence : Bool
    safetyAndBiosecurityNeedAdmission : Bool
    identifiedEffectAndRecommendationRemainDistinct : Bool
    dietaryMetaAnalysisAutomaticallyProvesLitterBenefit : Bool

canonicalPoultryBiologicalInterventionBoundary : PoultryBiologicalInterventionBoundary
canonicalPoultryBiologicalInterventionBoundary =
  poultry-biological-intervention-boundary true true true true true true false
