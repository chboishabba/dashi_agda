module DASHI.Environment.PluralSustainableLandManagementTraditionsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.SustainableAgricultureManagementExact as Base
import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources

------------------------------------------------------------------------
-- PLURAL SUSTAINABLE LAND-MANAGEMENT TRADITIONS
--
-- This module extends, rather than replaces, the canonical sustainable-
-- agriculture management owner.  It follows Docs/SourceAttributionPolicy.md:
--
--   external source claim/data
--     != DASHI reconstruction
--     != DASHI cross-source inference
--     != DASHI theorem
--     != recommendation/promotion.
--
-- It additionally separates:
--
--   technical management method
--     != social/political agrarian movement
--     != religious/ethical agrarian constraint
--     != certification regime
--     != empirical outcome.
------------------------------------------------------------------------

data TraditionKind : Set where
  technicalMethod
  forestryMethod
  agroforestryMethod
  soilCarbonMethod
  movementFramework
  sovereigntyFramework
  religiousAgrarianPractice
  ethicalConstraintFramework
  certificationTradition
  umbrellaManagementFramework : TraditionKind

data AdditionalPracticeFamily : Set where
  biodynamicAgriculture
  syntropicAgriculture
  successionalAgroforestry
  huegelkultur
  silviculture
  closeToNatureForestry
  coppicePollardManagement
  assistedNaturalRegeneration
  regenerativeAgriculture
  carbonFarming
  conservationAgriculture
  naturalFarmingIndia
  livestockIntegratedNaturalFarming
  peasantAgroecology
  foodSovereignty
  zapatistaAgroecology
  nativeSeedSovereignty
  iskconCowProtectedAgriculture
  jainAhimsaAgrarianEthics : AdditionalPracticeFamily

data SourceStrength : Set where
  primaryMovementSource
  primaryInstitutionalSource
  primaryStandardsSource
  officialPracticeSource
  peerReviewedScholarship
  universityExtension
  secondaryScholarlyReconstruction
  unresolvedPrimarySource : SourceStrength

record TraditionSource : Set where
  constructor tradition-source
  field
    family : AdditionalPracticeFamily
    traditionKind : TraditionKind
    authorsOrCommunity : String
    title : String
    venue : String
    year : Nat
    identifier : String
    strength : SourceStrength
    boundedReading : String
    excludedPromotion : String

open TraditionSource public

------------------------------------------------------------------------
-- Source-bounded anchors.
------------------------------------------------------------------------

biodynamicDemeter2026 : TraditionSource
biodynamicDemeter2026 = tradition-source
  biodynamicAgriculture certificationTradition
  "Biodynamic Federation Demeter International"
  "International Demeter Biodynamic Standard"
  "Demeter International" 2026
  "International Demeter Biodynamic Standard, English version 2026"
  primaryStandardsSource
  "Biodynamic management is a distinct certified practice tradition with whole-farm, soil-fertility, biodiversity, preparation and animal-husbandry requirements; the standard traces its historical knowledge tradition to Rudolf Steiner's 1924 Agricultural Course."
  "Certification or biodynamic identity does not by itself prove any particular yield, soil-carbon, health, metaphysical, or causal-effect claim."

syntropicGotsch : TraditionSource
syntropicGotsch = tradition-source
  syntropicAgriculture agroforestryMethod
  "Ernst Götsch / Agenda Götsch"
  "What is Syntropic Farming?"
  "Agenda Götsch, official Syntropic Farming site" 2019
  "Canonical Agenda Götsch practice description"
  officialPracticeSource
  "Syntropic agriculture is described as successional agroforestry translating ecosystem succession, stratification, continuous occupation and biomass-management processes into farming interventions."
  "The practice description does not by itself prove universal soil-carbon gain, input independence, yield, biodiversity, water or profitability effects."

successionalAgroforestryAlias : TraditionSource
successionalAgroforestryAlias = tradition-source
  successionalAgroforestry agroforestryMethod
  "Agenda Götsch"
  "Syntropic Agriculture / successional agroforestry terminology"
  "Agenda Götsch" 2019
  "Canonical Agenda Götsch terminology"
  officialPracticeSource
  "Successional agroforestry is an alternate descriptor used in the source lineage for syntropic agriculture."
  "Terminological relation does not identify every successional agroforestry system with every implementation of Götsch's method."

huegelkulturWSU : TraditionSource
huegelkulturWSU = tradition-source
  huegelkultur technicalMethod
  "Linda Chalker-Scott"
  "Hügelkultur: What Is It, and Should It Be Used in Home Gardens?"
  "Washington State University Extension" 2022
  "WSU Extension FS283E, revised December 2022"
  universityExtension
  "Hügelkultur is a mounded horticultural practice using woody debris and other organic material; the extension source explicitly reviews both origin and limited evidence for claimed benefits."
  "Practice identity does not prove superior fertility, water retention, carbon sequestration, or crop performance."

iskconAgrarianPractice : TraditionSource
iskconAgrarianPractice = tradition-source
  iskconCowProtectedAgriculture religiousAgrarianPractice
  "ISKCON / GBC Ministry of Cow Protection and Agriculture"
  "Cow Protection / Krishi Go Raksha agrarian practice"
  "ISKCON institutional sources" 2026
  "ISKCON Cow Protection; GBC Ministry of Cow Protection and Agriculture"
  primaryInstitutionalSource
  "ISKCON institutional practice links cow and bull lifetime protection, use of bull labour, farm self-reliance, dung/urine reuse, vegetarian food production and rural community life."
  "Religious or institutional commitment does not by itself prove agronomic superiority, environmental benefit, medical efficacy of by-products, or universal sustainability."

jainAgrarianEthics2025 : TraditionSource
jainAgrarianEthics2025 = tradition-source
  jainAhimsaAgrarianEthics ethicalConstraintFramework
  "Pankaj Jain"
  "Farming and Flora in Jainism"
  "Worldviews: Global Religions, Culture, and Ecology 29(2)" 2025
  "Pankaj Jain, Farming and Flora in Jainism, Worldviews 29(2), 2025"
  peerReviewedScholarship
  "Jain ahiṃsā and related ethical commitments create a nuanced constraint surface for agriculture because tillage and cultivation can harm plants, insects and soil organisms; Jain agricultural practice is therefore not reducible to one farming recipe."
  "Jain ethics must not be laundered into a claim that there is one canonical Jain farming technique or that a specified method is empirically optimal."

viaCampesinaPeasantAgroecology : TraditionSource
viaCampesinaPeasantAgroecology = tradition-source
  peasantAgroecology movementFramework
  "La Vía Campesina and allied small-scale food-producer movements"
  "Declaration of the International Forum for Agroecology, Nyéléni"
  "Nyéléni, Mali" 2015
  "Nyéléni 2015 Declaration on Agroecology; La Vía Campesina movement lineage"
  primaryMovementSource
  "Peasant agroecology is articulated as more than a menu of techniques: it is tied to producer knowledge, territory, collective rights, seeds, biodiversity and food sovereignty."
  "Movement self-description does not by itself establish a quantitative causal effect for any farm practice or transfer a DASHI theorem to La Vía Campesina."

viaCampesinaFoodSovereignty : TraditionSource
viaCampesinaFoodSovereignty = tradition-source
  foodSovereignty sovereigntyFramework
  "Nyéléni Food Sovereignty Forum / La Vía Campesina movement lineage"
  "Declaration of Nyéléni"
  "Nyéléni, Sélingué, Mali" 2007
  "Declaration of Nyéléni, 27 February 2007"
  primaryMovementSource
  "Food sovereignty is represented as a rights/governance framework concerning land, water, seeds, production, food systems and peoples' control, not as a soil-management technique."
  "Food-sovereignty commitment does not imply one prescribed agronomic method or prove a particular biophysical outcome."

zapatistaAgroecologyScholarship : TraditionSource
zapatistaAgroecologyScholarship = tradition-source
  zapatistaAgroecology movementFramework
  "Zapatista autonomous communities; empirical reconstruction by scholarship"
  "Agroecology, native maize and seed-sovereignty practices in Zapatista territories"
  "Chiapas movement/agroecology literature" 2020
  "Secondary scholarly reconstruction; exact primary EZLN practice locator remains claim-specific"
  secondaryScholarlyReconstruction
  "Scholarship reports Zapatista agroecological organisation, native-maize/milpa diversification, community seed banks and seed sovereignty within a wider autonomy project."
  "The secondary literature is not a substitute for an EZLN primary source, and Zapatismo must not be reduced to an agricultural technique or appropriated as a generic sustainability brand."

zapatistaSeedSovereignty : TraditionSource
zapatistaSeedSovereignty = tradition-source
  nativeSeedSovereignty sovereigntyFramework
  "Zapatista autonomous-community practice as reconstructed in scholarship"
  "Native maize, milpa diversification and community seed sovereignty"
  "Chiapas agroecology / seed-sovereignty scholarship" 2020
  "Primary-source attribution unresolved in this lane; secondary scholarly locator retained"
  unresolvedPrimarySource
  "Candidate source surface for community seed inventories, seed banks/living seed plots, native-maize diversification and opposition to proprietary control of germplasm."
  "No exact proposition is attributed directly to the EZLN until a recoverable primary locator is supplied."

indiaNaturalFarmingMission : TraditionSource
indiaNaturalFarmingMission = tradition-source
  naturalFarmingIndia umbrellaManagementFramework
  "Government of India, Ministry of Agriculture and Farmers' Welfare"
  "National Mission on Natural Farming"
  "Government of India" 2024
  "National Mission on Natural Farming; official Government of India programme"
  primaryInstitutionalSource
  "Natural farming is institutionally represented as chemical-free, locally adapted, livestock-integrated and biomass-recycling agriculture rooted in local agro-ecological knowledge."
  "Programme definition and policy promotion do not by themselves establish comparative causal superiority or identify all Indian natural-farming traditions as one technique."

------------------------------------------------------------------------
-- Forestry / carbon-oriented methods: structural slots.
-- These are typed now, but concrete source receipts remain separately supplied.
------------------------------------------------------------------------

record ForestSoilCarbonPractice : Set where
  constructor forest-soil-carbon-practice
  field
    family : AdditionalPracticeFamily
    woodyBiomassRetained : Bool
    livingRootsRetained : Bool
    litterReturnExpected : Bool
    soilDisturbanceManaged : Bool
    carbonOutcomeNeedsMeasurement : Bool
    sourceReference : String

open ForestSoilCarbonPractice public

syntropicForestSoilPattern : ForestSoilCarbonPractice
syntropicForestSoilPattern = forest-soil-carbon-practice
  syntropicAgriculture true true true true true
  "Agenda Götsch practice lineage; quantitative carbon outcome requires independent measurement"

huegelForestSoilPattern : ForestSoilCarbonPractice
huegelForestSoilPattern = forest-soil-carbon-practice
  huegelkultur true false true true true
  "WSU Extension FS283E; woody-debris mound practice, with claimed outcomes kept empirical"

------------------------------------------------------------------------
-- Movement/ethics/practice typing.
------------------------------------------------------------------------

record MovementAgrarianFrame : Set where
  constructor movement-agrarian-frame
  field
    source : TraditionSource
    landOrTerritory : Bool
    seedGovernance : Bool
    producerKnowledge : Bool
    collectiveOrganisation : Bool
    marketOrFoodSystemGovernance : Bool
    notReducibleToTechnique : Bool

open MovementAgrarianFrame public

viaCampesinaFrame : MovementAgrarianFrame
viaCampesinaFrame = movement-agrarian-frame
  viaCampesinaPeasantAgroecology true true true true true true

zapatistaFrame : MovementAgrarianFrame
zapatistaFrame = movement-agrarian-frame
  zapatistaAgroecologyScholarship true true true true true true

record EthicalAgrarianConstraint : Set where
  constructor ethical-agrarian-constraint
  field
    source : TraditionSource
    minimiseAnimalHarm : Bool
    minimiseSoilBiotaHarm : Bool
    animalLabourOrHusbandryRule : String
    inputOrConsumptionRule : String
    empiricalAgronomyStillSeparate : Bool

open EthicalAgrarianConstraint public

jainAhimsaConstraint : EthicalAgrarianConstraint
jainAhimsaConstraint = ethical-agrarian-constraint
  jainAgrarianEthics2025 true true
  "No single canonical husbandry system inferred; ahiṃsā constrains harm analysis"
  "Religious dietary/ethical practices remain distinct from agronomic mechanism"
  true

iskconCowProtectionConstraint : EthicalAgrarianConstraint
iskconCowProtectionConstraint = ethical-agrarian-constraint
  iskconAgrarianPractice true false
  "Lifetime cow/bull protection; institutional sources include humane bull labour and goshala care"
  "Farm self-reliance and vegetarian food-production commitments are source-attributed institutional aims"
  true

------------------------------------------------------------------------
-- Existing sustainable-management compatibility.
------------------------------------------------------------------------

data ExtendedManagementTechnique : Set where
  existingTechnique : Base.ManagementTechnique → ExtendedManagementTechnique
  additionalTechnique : AdditionalPracticeFamily → ExtendedManagementTechnique

record ExtendedManagementPractice : Set where
  constructor extended-management-practice
  field
    technique : ExtendedManagementTechnique
    sourceStage : Sources.ClaimStage
    sourceReference : String
    siteContext : String
    timingContext : String
    implementationReference : String

open ExtendedManagementPractice public

canonicalSyntropicManagement : ExtendedManagementPractice
canonicalSyntropicManagement = extended-management-practice
  (additionalTechnique syntropicAgriculture)
  Sources.externalSourceClaim
  "Agenda Götsch practice lineage"
  "site-specific; succession and strata explicit"
  "multi-year successional horizon"
  "species succession, stratification, pruning/biomass cycling and soil-cover implementation must be concretely specified"

canonicalBiodynamicManagement : ExtendedManagementPractice
canonicalBiodynamicManagement = extended-management-practice
  (additionalTechnique biodynamicAgriculture)
  Sources.externalSourceClaim
  "Demeter International Biodynamic Standard 2026"
  "farm individuality/site explicit"
  "whole-farm and seasonal management horizon"
  "certification/practice requirements must remain separate from empirical outcome evidence"

canonicalHuegelkulturManagement : ExtendedManagementPractice
canonicalHuegelkulturManagement = extended-management-practice
  (additionalTechnique huegelkultur)
  Sources.externalSourceClaim
  "WSU Extension FS283E"
  "bed/site and woody-material provenance explicit"
  "multi-year decomposition horizon"
  "mound geometry, woody material, soil layering and comparator must be specified"

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data MovementMeansTechniquePermission : Set where

data ReligiousEthicMeansAgronomicEffectPermission : Set where

data CertificationMeansCausalBenefitPermission : Set where

data SyntropicMeansMeasuredCarbonGainPermission : Set where

data HuegelMeansCarbonSequestrationPermission : Set where

data ZapatistaSecondarySourceMeansEZLNPrimaryQuotePermission : Set where

data ViaCampesinaClaimMeansDASHITheoremPermission : Set where

data JainismMeansSingleFarmingRecipePermission : Set where

data ISKCONMeansGenericVedicAgriculturePermission : Set where

movementIsNotAUniqueTechnique : MovementMeansTechniquePermission → ⊥
movementIsNotAUniqueTechnique ()

religiousEthicDoesNotProveAgronomicEffect : ReligiousEthicMeansAgronomicEffectPermission → ⊥
religiousEthicDoesNotProveAgronomicEffect ()

certificationDoesNotProveCausalBenefit : CertificationMeansCausalBenefitPermission → ⊥
certificationDoesNotProveCausalBenefit ()

syntropicIdentityDoesNotProveCarbonGain : SyntropicMeansMeasuredCarbonGainPermission → ⊥
syntropicIdentityDoesNotProveCarbonGain ()

huegelIdentityDoesNotProveCarbonSequestration : HuegelMeansCarbonSequestrationPermission → ⊥
huegelIdentityDoesNotProveCarbonSequestration ()

secondaryZapatistaLiteratureIsNotPrimaryEZLNQuotation :
  ZapatistaSecondarySourceMeansEZLNPrimaryQuotePermission → ⊥
secondaryZapatistaLiteratureIsNotPrimaryEZLNQuotation ()

viaCampesinaDoesNotOwnDASHITheorems : ViaCampesinaClaimMeansDASHITheoremPermission → ⊥
viaCampesinaDoesNotOwnDASHITheorems ()

jainEthicsDoesNotDefineOneUniversalFarmRecipe : JainismMeansSingleFarmingRecipePermission → ⊥
jainEthicsDoesNotDefineOneUniversalFarmRecipe ()

iskconPracticeIsNotGenericVedicAgriculture : ISKCONMeansGenericVedicAgriculturePermission → ⊥
iskconPracticeIsNotGenericVedicAgriculture ()

record PluralSustainableLandManagementBoundary : Set where
  constructor plural-sustainable-land-management-boundary
  field
    technicalMovementReligiousAndCertificationKindsRemainDistinct : Bool
    culturalAndPoliticalSourceOwnershipIsRetained : Bool
    primaryAndSecondarySourceStrengthRemainDistinct : Bool
    carbonClaimsRequireMeasuredCarbonCoordinate : Bool
    practiceIdentityDoesNotPromoteOutcome : Bool
    siteAndHistoryRemainFirstClass : Bool

canonicalPluralSustainableLandManagementBoundary :
  PluralSustainableLandManagementBoundary
canonicalPluralSustainableLandManagementBoundary =
  plural-sustainable-land-management-boundary true true true true true true
