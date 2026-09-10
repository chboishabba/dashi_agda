module DASHI.Environment.MosaicFireGrazingSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Governance.SteffensenCulturalFireAuthorityExact as CulturalFire

------------------------------------------------------------------------
-- MOSAIC FIRE / PATCH-BURN GRAZING SOURCE ATTRIBUTION
--
-- Attribution rule:
-- Indigenous cultural-fire authority/practice
--   != pyric-herbivory scientific literature
--   != generic prescribed-fire management
--   != DASHI cross-source reconstruction
--   != causal effect
--   != recommendation.
--
-- The existing Steffensen/Firesticks owner remains authoritative for the
-- knowledge/practice/Country-authority distinction.  This owner does not
-- reconstruct or generalise Country-specific cultural authority.
------------------------------------------------------------------------

data FireGrazingLineage : Set where
  pyricHerbivoryResearch
  patchBurnGrazingManagement
  genericPrescribedMosaicFire
  IndigenousCulturalBurningLineage : FireGrazingLineage

data EvidenceRelation : Set where
  conceptualMechanismSource
  directPatchBurnFieldStudy
  directPyricHerbivoryFieldStudy
  economicManagementStudy
  livestockSpeciesResponseStudy
  culturalAuthoritySourceOnly : EvidenceRelation

data PublicationForm : Set where
  peerReviewedArticle
  primaryFieldStudy
  economicAnalysis
  existingTypedAuthorityOwner : PublicationForm

record FireGrazingSource : Set where
  constructor fire-grazing-source
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    lineage : FireGrazingLineage
    relation : EvidenceRelation
    publicationForm : PublicationForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open FireGrazingSource public

fuhlendorfEngle2004 : FireGrazingSource
fuhlendorfEngle2004 = fire-grazing-source
  "S. D. Fuhlendorf; D. M. Engle"
  "Application of the fire–grazing interaction to restore a shifting mosaic on tallgrass prairie"
  "Journal of Applied Ecology 41:604–614"
  2004
  "DOI 10.1111/j.0021-8901.2004.00937.x"
  patchBurnGrazingManagement
  directPatchBurnFieldStudy
  primaryFieldStudy
  "Spatially discrete fire followed by focal grazing was experimentally used to generate a shifting vegetation mosaic in North American tallgrass prairie; outcomes were measured on the studied system."
  "Does not establish universal livestock, biodiversity, carbon, soil or wildfire benefits across other ecosystems, herbivores, fire regimes or cultural-management contexts."
  Attribution.externalSourceOwner

fuhlendorfEtAl2009 : FireGrazingSource
fuhlendorfEtAl2009 = fire-grazing-source
  "Samuel D. Fuhlendorf; David M. Engle; Jay Kerby; Robert Hamilton"
  "Pyric herbivory: rewilding landscapes through the recoupling of fire and grazing"
  "Conservation Biology 23(3):588–598"
  2009
  "DOI 10.1111/j.1523-1739.2008.01139.x"
  pyricHerbivoryResearch
  conceptualMechanismSource
  peerReviewedArticle
  "Frames fire and herbivory as spatially and temporally coupled disturbances capable of producing shifting mosaics rather than independent uniform treatments."
  "Conceptual recoupling does not identify every mosaic burn as pyric herbivory or establish benefit in every ecosystem."
  Attribution.externalSourceOwner

pyricNutrientHeterogeneity2024 : FireGrazingSource
pyricNutrientHeterogeneity2024 = fire-grazing-source
  "authors recoverable through DOI"
  "Restorative pyric herbivory practices in shrub-encroached grasslands enhance nutrient resource availability and spatial heterogeneity"
  "Agriculture, Ecosystems & Environment 372, 109072"
  2024
  "DOI 10.1016/j.agee.2024.109072"
  pyricHerbivoryResearch
  directPyricHerbivoryFieldStudy
  primaryFieldStudy
  "Field study reports altered soil nutrient availability and spatial heterogeneity under its prescribed-fire plus targeted-herbivory treatment in shrub-encroached grassland."
  "Does not establish the same nutrient response under different rainfall, soils, stocking, herbivore species, burn geometry or fire intensity."
  Attribution.externalSourceOwner

forageLivestock2024 : FireGrazingSource
forageLivestock2024 = fire-grazing-source
  "authors recoverable through DOI"
  "Improving forage nutritive value and livestock performance with spatially-patchy prescribed fire in grazed rangeland"
  "Agriculture, Ecosystems & Environment 368, 109004"
  2024
  "DOI 10.1016/j.agee.2024.109004"
  patchBurnGrazingManagement
  directPatchBurnFieldStudy
  primaryFieldStudy
  "Reports forage-quality, cattle patch-selection and livestock-performance responses under the studied spatially patchy prescribed-fire treatment."
  "Does not make recently burned forage preferable to every herbivore species or prove landscape-scale biodiversity/carbon outcomes."
  Attribution.externalSourceOwner

patchBurnEconomics2025 : FireGrazingSource
patchBurnEconomics2025 = fire-grazing-source
  "authors recoverable through DOI"
  "Patch-Burn Grazing: An Economic Analysis of Pyric Herbivory Rangeland Management by Cow–Calf Producers"
  "Rangeland Ecology & Management 98:41–48"
  2025
  "DOI 10.1016/j.rama.2024.07.007"
  patchBurnGrazingManagement
  economicManagementStudy
  economicAnalysis
  "Compares reported/estimated implementation costs and selected cow–calf economic benefits of patch-burn grazing with a traditional whole-pasture burn schedule under the study assumptions."
  "Economic estimates are not ecological validation, universal profitability, or evidence that the same costs/benefits transfer to another region or livestock system."
  Attribution.externalSourceOwner

multiSpeciesPatchBurn2026 : FireGrazingSource
multiSpeciesPatchBurn2026 = fire-grazing-source
  "authors recoverable through article"
  "Differential response and interactions of livestock species to patch burning in Mesquite-Oak Savanna"
  "Landscape Ecology 41, article 43"
  2026
  "https://link.springer.com/article/10.1007/s10980-026-02306-1"
  pyricHerbivoryResearch
  livestockSpeciesResponseStudy
  primaryFieldStudy
  "Reports species-specific spatial responses of cattle, sheep and goats under a patch-burning regime, demonstrating that herbivore response to recent burns is not uniform across livestock species."
  "Does not establish one generic grazer-selection response or transfer results beyond the studied Mesquite-Oak Savanna system."
  Attribution.externalSourceOwner

culturalFireAuthorityExistingOwner : FireGrazingSource
culturalFireAuthorityExistingOwner = fire-grazing-source
  "Victor Steffensen / Firesticks Alliance source lineage; exact authority typing delegated to existing owner"
  "Cultural fire knowledge/practice/authority boundary"
  "DASHI.Governance.SteffensenCulturalFireAuthorityExact"
  2020
  "Steffensen, Fire Country ISBN 9781741177268; Firesticks Alliance submission 0906 (2020)"
  IndigenousCulturalBurningLineage
  culturalAuthoritySourceOnly
  existingTypedAuthorityOwner
  "The existing owner distinguishes knowledge of cultural burning, permission to practise under authority, and Country-specific authority; technique knowledge does not create authority."
  "Must not be used to rename generic patch-burn grazing as Indigenous cultural burning, create Country authority, or universalise one governance structure."
  Attribution.externalSourceOwner

canonicalFireGrazingSources : List FireGrazingSource
canonicalFireGrazingSources =
  fuhlendorfEngle2004 ∷
  fuhlendorfEtAl2009 ∷
  pyricNutrientHeterogeneity2024 ∷
  forageLivestock2024 ∷
  patchBurnEconomics2025 ∷
  multiSpeciesPatchBurn2026 ∷
  culturalFireAuthorityExistingOwner ∷ []

------------------------------------------------------------------------
-- No-laundering barriers.
------------------------------------------------------------------------

data PatchBurnMeansCulturalBurningPermission : Set where
data CulturalTechniqueKnowledgeMeansCountryAuthorityPermission : Set where
data GreatPlainsResultMeansAustralianResultPermission : Set where
data CattleResponseMeansSheepGoatResponsePermission : Set where
data MosaicMeansBiodiversityBenefitPermission : Set where
data EconomicBenefitMeansEcologicalBenefitPermission : Set where

patchBurnDoesNotBecomeCulturalBurning : PatchBurnMeansCulturalBurningPermission → ⊥
patchBurnDoesNotBecomeCulturalBurning ()

techniqueKnowledgeDoesNotCreateCountryAuthority : CulturalTechniqueKnowledgeMeansCountryAuthorityPermission → ⊥
techniqueKnowledgeDoesNotCreateCountryAuthority ()

greatPlainsEvidenceDoesNotAutoTransferToAustralia : GreatPlainsResultMeansAustralianResultPermission → ⊥
greatPlainsEvidenceDoesNotAutoTransferToAustralia ()

cattleSelectionDoesNotDetermineOtherHerbivores : CattleResponseMeansSheepGoatResponsePermission → ⊥
cattleSelectionDoesNotDetermineOtherHerbivores ()

mosaicLabelDoesNotProveBiodiversityBenefit : MosaicMeansBiodiversityBenefitPermission → ⊥
mosaicLabelDoesNotProveBiodiversityBenefit ()

economicBenefitDoesNotProveEcologicalBenefit : EconomicBenefitMeansEcologicalBenefitPermission → ⊥
economicBenefitDoesNotProveEcologicalBenefit ()

culturalFireAuthoritySystem :
  CulturalFire.system ≡ CulturalFire.system
culturalFireAuthoritySystem = refl

record FireGrazingAttributionBoundary : Set where
  constructor fire-grazing-attribution-boundary
  field
    culturalFireAndPatchBurnGrazingRemainDistinct : Bool
    sourceClaimAndDashiSynthesisRemainDistinct : Bool
    mechanismAndOutcomeRemainDistinct : Bool
    speciesSpecificResponsesRemainDistinct : Bool
    culturalAuthorityDelegatedToExistingOwner : Bool
    adjacentScientificEvidenceCreatesCountryAuthority : Bool

canonicalFireGrazingAttributionBoundary : FireGrazingAttributionBoundary
canonicalFireGrazingAttributionBoundary =
  fire-grazing-attribution-boundary true true true true true false
