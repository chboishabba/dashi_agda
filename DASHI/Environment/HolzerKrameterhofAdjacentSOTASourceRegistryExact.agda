module DASHI.Environment.HolzerKrameterhofAdjacentSOTASourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- KRAMETERHOF-ADJACENT SOTA SOURCE REGISTRY
--
-- Attribution rule:
-- external source claim/data != practitioner report != DASHI reconstruction
-- != cross-source inference != causal validation != recommendation.
--
-- These sources are mechanism- or management-adjacent evidence.  None is
-- silently promoted to a direct experimental validation of Krameterhof.
------------------------------------------------------------------------

data AdjacentEvidenceDomain : Set where
  aquacultureWastewaterManagement
  natureBasedAquacultureTreatment
  constructedWetlandTreatment
  silvopastoralAgroforestry
  passiveUndergroundFoodStorage : AdjacentEvidenceDomain

data AdjacentEvidenceRelation : Set where
  mechanismAdjacent
  managementFamilyAdjacent
  engineeringAnalogue
  directExternalSystemStudy
  systematicReviewOfAdjacentClass : AdjacentEvidenceRelation

data AdjacentPublicationForm : Set where
  review
  systematicReview
  fieldStudy
  engineeringAssessment : AdjacentPublicationForm

record AdjacentSOTASource : Set where
  constructor adjacent-sota-source
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    domain : AdjacentEvidenceDomain
    relation : AdjacentEvidenceRelation
    publicationForm : AdjacentPublicationForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open AdjacentSOTASource public

freshwaterAquacultureWastewaterReview2025 : AdjacentSOTASource
freshwaterAquacultureWastewaterReview2025 = adjacent-sota-source
  "authors recoverable through DOI"
  "Advancements in freshwater aquaculture wastewater management: A comprehensive review"
  "Aquaculture 594, 741346"
  2025
  "DOI 10.1016/j.aquaculture.2024.741346"
  aquacultureWastewaterManagement
  systematicReviewOfAdjacentClass
  review
  "Reviews freshwater aquaculture wastewater impacts and treatment/management strategies; nutrient-rich effluent, solids and eutrophication risk are distinct management coordinates."
  "Does not validate Krameterhof pond cascades, planted ponds, open channels or any claimed regeneration effect."
  Attribution.externalSourceOwner

troutNatureBasedTreatment2025 : AdjacentSOTASource
troutNatureBasedTreatment2025 = adjacent-sota-source
  "Marcin Sidoruk; Ireneusz Cymes; Andrzej Skwierawski; Mirosław Skorbiłowicz"
  "Evaluating the effectiveness of natural wastewater treatment systems from intensive trout aquaculture facilities"
  "Water Resources and Industry 34, 100314"
  2025
  "DOI 10.1016/j.wri.2025.100314"
  natureBasedAquacultureTreatment
  directExternalSystemStudy
  fieldStudy
  "Evaluates treatment ditches and sedimentation ponds as nature-based treatment stages for effluent from four intensive trout farms."
  "A study of trout-farm treatment ditches/sedimentation ponds is adjacent evidence, not a direct test of Krameterhof pond sequences or open-channel reaeration."
  Attribution.externalSourceOwner

constructedWetlandVermifiltrationReview2026 : AdjacentSOTASource
constructedWetlandVermifiltrationReview2026 = adjacent-sota-source
  "authors recoverable through DOI"
  "Nature-based wastewater treatment technologies: A comprehensive review of constructed wetlands and vermifiltration"
  "Cleaner Water 5, 100204"
  2026
  "DOI 10.1016/j.clwat.2026.100204"
  constructedWetlandTreatment
  mechanismAdjacent
  systematicReview
  "Reviews constructed wetlands and vermifiltration across wastewater classes, with distinct nutrient, solids, pollutant and pathogen-removal coordinates and explicit remaining scale-up gaps."
  "Planted treatment systems share candidate mechanisms with vegetated ponds but are not definitionally the same intervention and do not validate Krameterhof performance."
  Attribution.externalSourceOwner

pondAquacultureTreatmentReview2024 : AdjacentSOTASource
pondAquacultureTreatmentReview2024 = adjacent-sota-source
  "Simon Tabrett; Ian Ramsay; Brian Paterson; Michele A. Burford"
  "A review of the benefits and limitations of waste nutrient treatment in aquaculture pond facilities"
  "Reviews in Aquaculture 16(4), 1766-1786"
  2024
  "DOI 10.1111/raq.12921"
  constructedWetlandTreatment
  systematicReviewOfAdjacentClass
  review
  "Reviews settlement ponds, constructed wetlands and other pond-aquaculture treatment routes. Constructed-wetland performance depends on hydraulic design, retention time, vegetation, microbial processes and scale; reported nutrient removal is variable and wetlands can also remobilise nutrients."
  "Does not validate Krameterhof planted ponds or establish that vegetation, detention or repeated reuse necessarily improves a downstream pond."
  Attribution.externalSourceOwner

silvopastureSystematicReview2025 : AdjacentSOTASource
silvopastureSystematicReview2025 = adjacent-sota-source
  "Ripamonti et al.; full author list recoverable through DOI"
  "Effects of tree presence on forage yield and nutritive value in agroforestry livestock systems: a global systematic review"
  "Agroforestry Systems 99, article 110"
  2025
  "DOI 10.1007/s10457-025-01214-8"
  silvopastoralAgroforestry
  managementFamilyAdjacent
  systematicReview
  "Global systematic review finds tree effects on forage systems are context-dependent, including light limitation and nutrient competition as important mechanisms."
  "Does not make terrace embankment grazing, coppice-with-standards or Krameterhof agroforestry empirically equivalent to the reviewed systems."
  Attribution.externalSourceOwner

coolingAtlasUnderground2025 : AdjacentSOTASource
coolingAtlasUnderground2025 = adjacent-sota-source
  "authors recoverable through DOI"
  "A Cooling Atlas for preserving fruit and vegetables in low- and middle-income countries"
  "Journal of Agriculture and Food Research"
  2025
  "DOI 10.1016/j.jafr.2025.101806"
  passiveUndergroundFoodStorage
  engineeringAnalogue
  review
  "Reviews low-energy food-cooling approaches; underground cooling is described as using lower and more stable ground temperatures, while ventilation remains necessary to control moisture, mould and crop gases."
  "Does not measure the Krameterhof earth cellar, prove its energy saving, or establish product-specific storage safety."
  Attribution.externalSourceOwner

earthCoupledPotatoStorage2022 : AdjacentSOTASource
earthCoupledPotatoStorage2022 = adjacent-sota-source
  "authors recoverable through DOI"
  "Life Cycle Saving Analysis of an Earth-Coupled Building without and with Roof Evaporative Cooling for Energy Efficient Potato Storage Application"
  "Energies 15(11), 4076"
  2022
  "DOI 10.3390/en15114076"
  passiveUndergroundFoodStorage
  engineeringAnalogue
  engineeringAssessment
  "Assesses earth coupling and evaporative cooling as passive means of reducing refrigeration cooling load in modelled potato-storage applications across multiple climates."
  "Does not determine Krameterhof cellar performance, construction cost, humidity safety, ventilation adequacy or product-specific shelf life."
  Attribution.externalSourceOwner

canonicalKrameterhofAdjacentSources : List AdjacentSOTASource
canonicalKrameterhofAdjacentSources =
  freshwaterAquacultureWastewaterReview2025 ∷
  troutNatureBasedTreatment2025 ∷
  constructedWetlandVermifiltrationReview2026 ∷
  pondAquacultureTreatmentReview2024 ∷
  silvopastureSystematicReview2025 ∷
  coolingAtlasUnderground2025 ∷
  earthCoupledPotatoStorage2022 ∷ []

------------------------------------------------------------------------
-- Non-laundering barriers.
------------------------------------------------------------------------

data AdjacentStudyMeansKrameterhofValidationPermission : Set where
data SharedMechanismMeansSamePracticePermission : Set where
data ReviewMeansMeasuredSiteEffectPermission : Set where
data PassiveAnalogueMeansEnergySavingPermission : Set where
data SilvopastureReviewMeansHolzerAgroforestryOutcomePermission : Set where

adjacentEvidenceDoesNotBecomeKrameterhofValidation :
  AdjacentStudyMeansKrameterhofValidationPermission → ⊥
adjacentEvidenceDoesNotBecomeKrameterhofValidation ()

sharedMechanismDoesNotIdentifySamePractice :
  SharedMechanismMeansSamePracticePermission → ⊥
sharedMechanismDoesNotIdentifySamePractice ()

reviewDoesNotBecomeMeasuredSiteEffect :
  ReviewMeansMeasuredSiteEffectPermission → ⊥
reviewDoesNotBecomeMeasuredSiteEffect ()

passiveStorageAnalogueDoesNotProveEnergySaving :
  PassiveAnalogueMeansEnergySavingPermission → ⊥
passiveStorageAnalogueDoesNotProveEnergySaving ()

silvopastureLiteratureDoesNotPayHolzerOutcome :
  SilvopastureReviewMeansHolzerAgroforestryOutcomePermission → ⊥
silvopastureLiteratureDoesNotPayHolzerOutcome ()

record KrameterhofAdjacentAttributionBoundary : Set where
  constructor krameterhof-adjacent-attribution-boundary
  field
    practitionerReportAndAdjacentLiteratureRemainDistinct : Bool
    physicalMechanismAndManagementIdentityRemainDistinct : Bool
    literatureSynthesisAndSiteMeasurementRemainDistinct : Bool
    dashiCrossSourceInferenceRemainsDashiOwned : Bool
    adjacentEvidenceAutomaticallyValidatesKrameterhof : Bool

canonicalKrameterhofAdjacentAttributionBoundary :
  KrameterhofAdjacentAttributionBoundary
canonicalKrameterhofAdjacentAttributionBoundary =
  krameterhof-adjacent-attribution-boundary true true true true false
