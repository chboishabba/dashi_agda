module DASHI.Environment.NaturalBiologicalCompostInterventionAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.BerkeleyRapidThermophilicCompostingExact as Berkeley
import DASHI.Environment.PoultryBiologicalInterventionExact as Poultry
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Causal

------------------------------------------------------------------------
-- NATURAL / BIOLOGICAL INTERVENTION + COMPOST PROCESS ATLAS
--
-- Source-attribution rule inherited from Docs/SourceAttributionPolicy.md:
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != DASHI theorem != promotion/recommendation.
--
-- Literature calibration retained as source metadata, not theorem content:
-- * Berkeley/Raabe rapid composting is inherited from the canonical owner.
-- * 2026 review "On-farm composting systems for regenerative agriculture"
--   compares vermicomposting, bokashi, Johnson-Su, hot composting, windrows,
--   compost teas/extracts and stresses uneven evidence across methods.
-- * 2025 comprehensive compost-tea review (DOI 10.1016/j.eti.2025.104137)
--   finds preparation/application dependence and incomplete standardisation.
-- * poultry microbial interventions reuse the route-indexed canonical owner;
--   dietary probiotic evidence is not transferred to litter/surface treatment.
------------------------------------------------------------------------

data InterventionClass : Set where
  rapidThermophilicCompost
  bokashiFermentation
  johnsonSuBioreactor
  vermicomposting
  aeratedCompostTea
  nonAeratedCompostTea
  compostExtract
  mycorrhizalInoculation
  rhizobialInoculation
  trichodermaIntervention
  entomopathogenicFungus
  predatorBiocontrol
  parasitoidBiocontrol
  poultryFeedProbiotic
  poultryWaterProbiotic
  poultryLitterMicrobialAmendment
  poultrySurfaceMicrobialAmendment
  poultryFermentedFeed
  manureBiologicalTreatment : InterventionClass

data InterventionRoute : Set where
  solidSoilAmendment
  liquidSoilDrench
  foliarApplication
  seedOrRootInoculation
  feedAdministration
  drinkingWaterAdministration
  litterApplication
  environmentalSurfaceApplication
  manureTreatment
  biologicalRelease : InterventionRoute

data TargetCoordinate : Set where
  soilOrganicMatter
  soilCarbon
  nutrientAvailability
  soilMicrobiome
  rootColonisation
  plantGrowth
  diseaseSuppression
  pestSuppression
  pathogenCarriage
  litterPH
  litterMoisture
  ammonia
  odourVOC
  animalPerformance
  animalWelfare
  greenhouseGasFlux
  carbonRetention
  nitrogenRetention : TargetCoordinate

data EvidenceTier : Set where
  sourceDescription
  mechanisticHypothesis
  controlledExperiment
  fieldExperiment
  systematicReview
  metaAnalysis
  identifiedCausalEffect
  promotedRecommendation : EvidenceTier

record InterventionIdentity : Set where
  constructor intervention-identity
  field
    interventionClass : InterventionClass
    route : InterventionRoute
    biologicalOrProcessIdentity : String
    formulationOrFeedstock : String
    doseOrApplicationRate : String
    viabilityOrProcessQuality : String
    timing : String
    siteHistory : String
    sourceStage : Sources.ClaimStage
    sourceLocator : String
    boundedSourceReading : String
    excludedPromotion : String

open InterventionIdentity public

record InterventionOutcomeEvidence : Set where
  constructor intervention-outcome-evidence
  field
    intervention : InterventionIdentity
    target : TargetCoordinate
    evidenceTier : EvidenceTier
    comparator : String
    populationOrSite : String
    measurementMethod : String
    resultReference : String
    uncertaintyOrHeterogeneity : String
    transferScope : String

open InterventionOutcomeEvidence public

------------------------------------------------------------------------
-- Canonical process/intervention identities.
------------------------------------------------------------------------

berkeleyRapidCompostIdentity : InterventionIdentity
berkeleyRapidCompostIdentity = intervention-identity
  rapidThermophilicCompost
  solidSoilAmendment
  "Robert D. Raabe / UC Berkeley rapid aerobic composting lineage"
  "mixed organic feedstocks; exact mixture batch-specific"
  "batch-specific"
  "temperature, oxygen, moisture, turning and maturity receipts required"
  "rapid turning schedule; exact implementation explicit"
  "site/batch history explicit"
  Sources.externalSourceClaim
  "DASHI.Environment.BerkeleyRapidThermophilicCompostingExact"
  "Rapid aerobic composting process lineage only."
  "Does not establish maturity, pathogen elimination, carbon sequestration or soil benefit."

bokashiIdentity : InterventionIdentity
bokashiIdentity = intervention-identity
  bokashiFermentation
  solidSoilAmendment
  "lactic-acid-dominant fermented organic matter / bokashi practice family"
  "feedstock and inoculant recipe explicit"
  "batch/application specific"
  "fermentation endpoint, pH, feedstock and inoculant provenance required"
  "fermentation and soil-incorporation timing explicit"
  "site/feedstock history explicit"
  Sources.externalSourceClaim
  "2026 On-farm composting systems for regenerative agriculture review"
  "Bokashi is represented as a lactic-acid fermentation organic-waste treatment with evidence distinct from aerobic composting."
  "Does not prove superior carbon retention, yield, disease suppression or soil benefit at every site."

johnsonSuIdentity : InterventionIdentity
johnsonSuIdentity = intervention-identity
  johnsonSuBioreactor
  solidSoilAmendment
  "Johnson-Su static aerated compost / bioreactor practice family"
  "feedstock and reactor geometry explicit"
  "batch/application specific"
  "maturity, process history and microbial-product quality required"
  "long-duration static curing / batch history explicit"
  "site/reactor history explicit"
  Sources.externalSourceClaim
  "2026 On-farm composting systems for regenerative agriculture review; stronger protocol-specific primary locator required per implementation"
  "Practice family only; typed representation does not import advocacy claims as effects."
  "Does not establish a universal soil-microbiome, carbon, yield or disease-suppression effect."

vermicompostIdentity : InterventionIdentity
vermicompostIdentity = intervention-identity
  vermicomposting
  solidSoilAmendment
  "earthworm-mediated organic-matter processing / vermicompost"
  "earthworm species, substrate and process conditions explicit"
  "application-rate specific"
  "maturity, substrate, nutrient and contamination quality required"
  "process and application timing explicit"
  "site/substrate history explicit"
  Sources.externalSourceClaim
  "Sande et al. 2024 Frontiers in Agronomy DOI 10.3389/fagro.2024.1422876; 2026 on-farm compost review"
  "Vermicompost is a distinct organic-amendment process with context-dependent nutrient/soil effects."
  "Does not imply universal yield, carbon or soil-health superiority."

aeratedCompostTeaIdentity : InterventionIdentity
aeratedCompostTeaIdentity = intervention-identity
  aeratedCompostTea
  foliarApplication
  "aerated compost tea"
  "compost source, water, additives and brewing conditions explicit"
  "application-rate specific"
  "oxygenation, brew time, microbial/pathogen quality and source compost required"
  "brew and application timing explicit"
  "host/pathogen/site history explicit"
  Sources.externalSourceClaim
  "Compost tea review DOI 10.1016/j.eti.2025.104137; 2026 disease-suppression review"
  "Preparation and application parameters are first-class because efficacy is heterogeneous."
  "Does not prove disease suppression, growth promotion or microbiome benefit for an unspecified recipe/site."

------------------------------------------------------------------------
-- Route-specific poultry adapters reuse the canonical poultry owner.
------------------------------------------------------------------------

fromPoultry : Poultry.BiologicalIntervention → InterventionIdentity
fromPoultry p = intervention-identity
  (routeClass p)
  (routeAtlas (Poultry.route p))
  (Poultry.organismOrStrain p)
  (Poultry.formulation p)
  (Poultry.doseOrConcentration p)
  (Poultry.viabilityOrQualityReference p)
  (Poultry.timingAndDuration p)
  (Poultry.housingContext p)
  (Poultry.sourceStage p)
  (Poultry.provenanceReference p)
  "Route-specific poultry biological intervention inherited from canonical owner."
  "Evidence does not transfer across feed, water, litter, surface, fermented-feed or manure routes without a receipt."
  where
  routeClass : Poultry.BiologicalIntervention → InterventionClass
  routeClass q with Poultry.route q
  ... | Poultry.feedRoute = poultryFeedProbiotic
  ... | Poultry.drinkingWaterRoute = poultryWaterProbiotic
  ... | Poultry.gavageRoute = poultryFeedProbiotic
  ... | Poultry.respiratoryOrNasalRoute = poultrySurfaceMicrobialAmendment
  ... | Poultry.litterOrBeddingInoculation = poultryLitterMicrobialAmendment
  ... | Poultry.environmentalSurfaceApplication = poultrySurfaceMicrobialAmendment
  ... | Poultry.fermentedFeedRoute = poultryFermentedFeed
  ... | Poultry.manureOrCompostTreatment = manureBiologicalTreatment

  routeAtlas : Poultry.AdministrationRoute → InterventionRoute
  routeAtlas Poultry.feedRoute = feedAdministration
  routeAtlas Poultry.drinkingWaterRoute = drinkingWaterAdministration
  routeAtlas Poultry.gavageRoute = feedAdministration
  routeAtlas Poultry.respiratoryOrNasalRoute = environmentalSurfaceApplication
  routeAtlas Poultry.litterOrBeddingInoculation = litterApplication
  routeAtlas Poultry.environmentalSurfaceApplication = environmentalSurfaceApplication
  routeAtlas Poultry.fermentedFeedRoute = feedAdministration
  routeAtlas Poultry.manureOrCompostTreatment = manureTreatment

------------------------------------------------------------------------
-- Causal experiment admission.
------------------------------------------------------------------------

record AtlasCausalBinding : Set₂ where
  constructor atlas-causal-binding
  field
    intervention : InterventionIdentity
    causalIdentity : Causal.SituatedInterventionIdentity
    identityWeldReference : String
    comparatorReference : String
    outcomeReference : String
    populationReference : String
    horizonReference : String
    assignmentOrIdentificationReference : String
    statisticalRealisationReference : String

open AtlasCausalBinding public

------------------------------------------------------------------------
-- WrongType / non-promotion barriers.
------------------------------------------------------------------------

data NaturalMeansSafePermission : Set where
data MicrobialMeansBeneficialPermission : Set where
data GenusMeansStrainPermission : Set where
data ProcessNameMeansProductQualityPermission : Set where
data CompostTeaMeansDiseaseSuppressionPermission : Set where
data BokashiMeansCarbonRetentionPermission : Set where
data JohnsonSuMeansMicrobiomeImprovementPermission : Set where
data VermicompostMeansYieldGainPermission : Set where
data InoculationMeansColonisationPermission : Set where
data LabEffectMeansFieldEffectPermission : Set where
data OneRouteMeansAnotherRoutePermission : Set where
data OutcomeEvidenceMeansRecommendationPermission : Set where

naturalDoesNotProveSafety : NaturalMeansSafePermission → ⊥
naturalDoesNotProveSafety ()

microbialDoesNotProveBenefit : MicrobialMeansBeneficialPermission → ⊥
microbialDoesNotProveBenefit ()

genusDoesNotIdentifyStrainEffect : GenusMeansStrainPermission → ⊥
genusDoesNotIdentifyStrainEffect ()

processNameDoesNotCertifyProductQuality : ProcessNameMeansProductQualityPermission → ⊥
processNameDoesNotCertifyProductQuality ()

compostTeaDoesNotDefinitionallySuppressDisease : CompostTeaMeansDiseaseSuppressionPermission → ⊥
compostTeaDoesNotDefinitionallySuppressDisease ()

bokashiDoesNotDefinitionallyRetainMoreCarbon : BokashiMeansCarbonRetentionPermission → ⊥
bokashiDoesNotDefinitionallyRetainMoreCarbon ()

johnsonSuDoesNotDefinitionallyImproveMicrobiome : JohnsonSuMeansMicrobiomeImprovementPermission → ⊥
johnsonSuDoesNotDefinitionallyImproveMicrobiome ()

vermicompostDoesNotDefinitionallyIncreaseYield : VermicompostMeansYieldGainPermission → ⊥
vermicompostDoesNotDefinitionallyIncreaseYield ()

inoculationDoesNotProveColonisation : InoculationMeansColonisationPermission → ⊥
inoculationDoesNotProveColonisation ()

labEffectDoesNotAutomaticallyTransferToField : LabEffectMeansFieldEffectPermission → ⊥
labEffectDoesNotAutomaticallyTransferToField ()

routeEvidenceDoesNotTransferByName : OneRouteMeansAnotherRoutePermission → ⊥
routeEvidenceDoesNotTransferByName ()

outcomeEvidenceDoesNotAutomaticallyPromoteRecommendation : OutcomeEvidenceMeansRecommendationPermission → ⊥
outcomeEvidenceDoesNotAutomaticallyPromoteRecommendation ()

record NaturalBiologicalCompostAtlasBoundary : Set where
  constructor natural-biological-compost-atlas-boundary
  field
    sourceAttributionAndDashiSynthesisDistinct : Bool
    organismStrainFormulationRouteDoseRemainFirstClass : Bool
    compostProcessAndProductQualityRemainDistinct : Bool
    labFieldAndReviewEvidenceRemainDistinct : Bool
    causalEffectNeedsExplicitEstimandBinding : Bool
    recommendationNeedsSeparatePromotion : Bool
    naturalLabelAutomaticallyProvesSafety : Bool
    biologicalLabelAutomaticallyProvesBenefit : Bool

canonicalNaturalBiologicalCompostAtlasBoundary : NaturalBiologicalCompostAtlasBoundary
canonicalNaturalBiologicalCompostAtlasBoundary =
  natural-biological-compost-atlas-boundary true true true true true true false false
