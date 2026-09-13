module DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION POLICY APPLIED TO SUSTAINABLE AGRICULTURE
--
-- Mirrors Docs/SourceAttributionPolicy.md:
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != new DASHI theorem != promotion/external adjudication.
------------------------------------------------------------------------

data ClaimStage : Set where
  externalSourceClaim
  dashiReconstruction
  dashiCrossSourceInference
  dashiTheorem
  promotedRecommendation : ClaimStage

data SourceKind : Set where
  intergovernmentalFramework
  governmentPracticeStandard
  governmentExtension
  scholarlyOrTechnicalNote
  existingTypedOwner : SourceKind

data PracticeFamily : Set where
  agroecologyFramework
  integratedPestManagement
  coverCropping
  conservationNoTill
  conservationCropRotation
  agroforestry
  silvopasture
  prescribedGrazing
  organicSoilHealthManagement
  koreanNaturalFarming
  permacultureDesign : PracticeFamily

record SustainableAgricultureSource : Set where
  constructor sustainable-agriculture-source
  field
    family : PracticeFamily
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    kind : SourceKind
    boundedReading : String
    excludedPromotion : String

open SustainableAgricultureSource public

faoAgroecology10Elements : SustainableAgricultureSource
faoAgroecology10Elements = sustainable-agriculture-source
  agroecologyFramework
  "Food and Agriculture Organization of the United Nations"
  "The 10 Elements of Agroecology"
  "FAO Agroecology Knowledge Hub / FAO Council framework"
  2019
  "FAO Council 163rd Session; canonical FAO Agroecology Knowledge Hub"
  intergovernmentalFramework
  "Framework characterising agroecological transitions through diversity, synergies, efficiency, recycling, resilience, co-creation of knowledge, human/social values, culture/food traditions, responsible governance, and circular/solidarity economy."
  "Does not prove that every practice labelled agroecological improves every environmental, social, economic, yield, health, or resilience endpoint."

faoIPM : SustainableAgricultureSource
faoIPM = sustainable-agriculture-source
  integratedPestManagement
  "Food and Agriculture Organization of the United Nations"
  "Integrated Pest Management"
  "FAO Pest and Pesticide Management"
  2026
  "Canonical FAO IPM page"
  intergovernmentalFramework
  "IPM integrates biological, physical, cultural/crop-specific and, where appropriate, chemical measures using agroecosystem analysis and action thresholds while seeking to minimise pesticide risks."
  "Does not prove that a particular IPM programme controls a particular pest, is economically optimal, or eliminates pesticide use."

nrcsCoverCrop340 : SustainableAgricultureSource
nrcsCoverCrop340 = sustainable-agriculture-source
  coverCropping
  "USDA Natural Resources Conservation Service"
  "Cover Crop (Ac.) (340) Conservation Practice Standard"
  "NRCS Conservation Practice Standards"
  2024
  "NRCS CPS 340"
  governmentPracticeStandard
  "Defines cover cropping as planting grasses, legumes or other herbaceous species to protect and improve soil when cropland would otherwise be bare, with local standards required for implementation."
  "Does not prove a universal quantitative erosion, carbon, yield, water or nutrient benefit for every site or mixture."

nrcsNoTill329 : SustainableAgricultureSource
nrcsNoTill329 = sustainable-agriculture-source
  conservationNoTill
  "USDA Natural Resources Conservation Service"
  "No till system to increase soil health and soil organic matter content (E329D)"
  "NRCS Conservation Stewardship Program"
  2026
  "NRCS E329D"
  governmentPracticeStandard
  "Management enhancement focused on increasing plant diversity and minimising soil disturbance in no-till systems."
  "Does not prove that no-till is superior on every soil, crop, weed-management system, climate, or time horizon."

nrcsCropRotation328 : SustainableAgricultureSource
nrcsCropRotation328 = sustainable-agriculture-source
  conservationCropRotation
  "USDA Natural Resources Conservation Service"
  "Conservation Crop Rotation (Ac.) (328) Conservation Practice Standard"
  "NRCS Conservation Practice Standards"
  2026
  "NRCS CPS 328"
  governmentPracticeStandard
  "Defines a planned crop sequence used for conservation purposes, subject to site-specific planning and state technical standards."
  "Does not prove that any arbitrary rotation delivers a specified pest, nitrogen, carbon, yield, or economic outcome."

usdaAgroforestry : SustainableAgricultureSource
usdaAgroforestry = sustainable-agriculture-source
  agroforestry
  "USDA Forest Service National Agroforestry Center"
  "National Agroforestry Center practice framework"
  "USDA National Agroforestry Center"
  2026
  "Canonical USDA National Agroforestry Center"
  governmentExtension
  "Recognises five major temperate agroforestry practices: windbreaks, riparian forest buffers, alley cropping, silvopasture, and forest farming."
  "Does not prove that every tree-crop/livestock mixture is agroforestry-admissible, locally appropriate, or environmentally beneficial."

usdaSilvopasture2025 : SustainableAgricultureSource
usdaSilvopasture2025 = sustainable-agriculture-source
  silvopasture
  "Katherine MacFarland; Samuel Feibel; Mark Batcheler; Annabelle Moore; Matthew M. Smith; Aaron Joslin"
  "Silvopasture: an agroforestry practice"
  "USDA Forest Service National Agroforestry Center, Agroforestry Note 8"
  2025
  "DOI 10.2737/NAC-AN-8"
  scholarlyOrTechnicalNote
  "Silvopasture intentionally integrates woody vegetation, forage and livestock on the same land and requires active management of those components."
  "Does not prove universal productivity, welfare, carbon, biodiversity, or profitability effects."

nrcsPrescribedGrazing528 : SustainableAgricultureSource
nrcsPrescribedGrazing528 = sustainable-agriculture-source
  prescribedGrazing
  "USDA Natural Resources Conservation Service"
  "Grazing Management (Code 528) Conservation Practice Standard"
  "NRCS Conservation Practice Standards"
  2025
  "NRCS CPS 528"
  governmentPracticeStandard
  "Management of vegetation harvest by grazing/browsing animals toward explicit ecological, economic and management objectives."
  "Does not prove that rotational or intensive grazing improves soil carbon, biodiversity, profitability or animal performance in every context."

nrcsOrganicHealthySoils : SustainableAgricultureSource
nrcsOrganicHealthySoils = sustainable-agriculture-source
  organicSoilHealthManagement
  "USDA Natural Resources Conservation Service"
  "Healthy Soils"
  "NRCS assistance for organic farmers"
  2026
  "Canonical NRCS organic soil-health guidance"
  governmentExtension
  "Identifies diverse rotations, cover crops, nutrient management, conservation tillage, year-round living roots and soil cover as soil-health practices usable in organic systems."
  "Does not identify organic certification itself with any one soil-health outcome or prove superiority of every organic management system."

knfExistingOwner : SustainableAgricultureSource
knfExistingOwner = sustainable-agriculture-source
  koreanNaturalFarming
  "Source attribution inherited through DASHI.Environment.KoreanNaturalFarmingExact"
  "Typed Korean Natural Farming practice owner"
  "DASHI source-bounded owner"
  2026
  "Consult imported owner for Cho/Koyama and University of Hawai'i attribution"
  existingTypedOwner
  "Reuses the existing source-bounded KNF preparation/application/evidence distinction."
  "Does not promote KNF practice identity to mechanism, outcome, causal effect or recommendation."

permacultureExistingOwner : SustainableAgricultureSource
permacultureExistingOwner = sustainable-agriculture-source
  permacultureDesign
  "Source attribution inherited through DASHI.Environment.LESObservationSourceRegistryExact"
  "Typed Holmgren permaculture observation/design owner"
  "DASHI source-bounded owner"
  2026
  "Consult imported LES source registry for Holmgren 2002 attribution"
  existingTypedOwner
  "Reuses Holmgren only for bounded design-principle calibration."
  "Does not attribute DASHI energy/resource loops, observer theorems, empirical dynamics or recommendations to Holmgren."

canonicalSustainableAgricultureSources : List SustainableAgricultureSource
canonicalSustainableAgricultureSources =
  faoAgroecology10Elements
  ∷ faoIPM
  ∷ nrcsCoverCrop340
  ∷ nrcsNoTill329
  ∷ nrcsCropRotation328
  ∷ usdaAgroforestry
  ∷ usdaSilvopasture2025
  ∷ nrcsPrescribedGrazing528
  ∷ nrcsOrganicHealthySoils
  ∷ knfExistingOwner
  ∷ permacultureExistingOwner
  ∷ []

record SustainableAgricultureAttributionBoundary : Set where
  constructor sustainable-agriculture-attribution-boundary
  field
    sourceIdentityPromotesOutcome : Bool
    sourceIdentityPromotesOutcomeIsFalse : sourceIdentityPromotesOutcome ≡ false
    sharedSustainabilityGoalMakesPracticesIdentical : Bool
    sharedSustainabilityGoalMakesPracticesIdenticalIsFalse : sharedSustainabilityGoalMakesPracticesIdentical ≡ false
    institutionalGuidanceIsSiteSpecificOutcomeProof : Bool
    institutionalGuidanceIsSiteSpecificOutcomeProofIsFalse : institutionalGuidanceIsSiteSpecificOutcomeProof ≡ false
    dashiCrossSourceInferenceMustRemainDashiOwned : Bool
    dashiCrossSourceInferenceMustRemainDashiOwnedIsTrue : dashiCrossSourceInferenceMustRemainDashiOwned ≡ true

canonicalSustainableAgricultureAttributionBoundary : SustainableAgricultureAttributionBoundary
canonicalSustainableAgricultureAttributionBoundary =
  sustainable-agriculture-attribution-boundary false refl false refl false refl true refl
