module DASHI.Environment.NitrogenPathwaySourceRegistryExact where

open import DASHI.Core.Prelude

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Physics.Plasma.PlasmaActivatedWaterAgricultureSourceRegistryExact as PAW
import DASHI.Environment.AquaticLivingInfrastructureSourceRegistryExact as Aquatic
import DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas as BNF
import DASHI.Environment.KNFSourceAttributionLineageExact as KNFAttribution

------------------------------------------------------------------------
-- NITROGEN PATHWAY SOURCE REGISTRY
--
-- This registry compares source entitlement, not pathway performance.
-- External literature owns only its bounded claims.  The common comparison
-- fibre and all cross-pathway equivalence/non-equivalence statements are DASHI
-- reconstruction/inference.
------------------------------------------------------------------------

data NitrogenSourceRole : Set where
  industrialAmmoniaSynthesis
  plasmaNitrogenFixation
  biologicalNitrogenFixation
  compostNitrogenMineralisation
  aquaponicNitrogenRecovery
  localNitrogenRecycling : NitrogenSourceRole

data NitrogenEvidenceForm : Set where
  reviewSource
  peerReviewedExperiment
  peerReviewedSynthesis
  existingSourceAtlas
  existingTypedLineage : NitrogenEvidenceForm

record NitrogenPathwaySource : Set where
  constructor nitrogen-pathway-source
  field
    role : NitrogenSourceRole
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    evidenceForm : NitrogenEvidenceForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open NitrogenPathwaySource public

haberBoschReview2024 : NitrogenPathwaySource
haberBoschReview2024 = nitrogen-pathway-source
  industrialAmmoniaSynthesis
  "Navid Erfani; Luqmanulhakim Baharudin; Matthew Watson"
  "Recent advances and intensifications in Haber-Bosch ammonia synthesis process"
  "Chemical Engineering and Processing - Process Intensification 204, 109962"
  2024
  "DOI 10.1016/j.cep.2024.109962"
  reviewSource
  "Haber-Bosch remains the predominant industrial ammonia-synthesis route; ammonia is a key nitrogen source for fertiliser manufacture, while process energy demand and upstream hydrogen source materially affect environmental performance."
  "Does not identify ammonia with a complete field fertiliser, assign one universal energy/emissions intensity, or prove site-specific agronomic performance."
  Attribution.externalSourceOwner

plasmaNitrogenSource : NitrogenPathwaySource
plasmaNitrogenSource = nitrogen-pathway-source
  plasmaNitrogenFixation
  (PAW.authorsOrInstitution PAW.robinsonStapelmann2024)
  (PAW.title PAW.robinsonStapelmann2024)
  (PAW.venue PAW.robinsonStapelmann2024)
  (PAW.year PAW.robinsonStapelmann2024)
  (PAW.identifier PAW.robinsonStapelmann2024)
  existingSourceAtlas
  (PAW.boundedReading PAW.robinsonStapelmann2024)
  (PAW.excludedPromotion PAW.robinsonStapelmann2024)
  (PAW.claimOwner PAW.robinsonStapelmann2024)

hungriaBNFSource : NitrogenPathwaySource
hungriaBNFSource = nitrogen-pathway-source
  biologicalNitrogenFixation
  (BNF.authors BNF.hungriaMendes2015)
  (BNF.title BNF.hungriaMendes2015)
  (BNF.venueOrPublisher BNF.hungriaMendes2015)
  (BNF.year BNF.hungriaMendes2015)
  (BNF.identifier BNF.hungriaMendes2015)
  existingSourceAtlas
  (BNF.importedRole BNF.hungriaMendes2015)
  (BNF.excludedPromotion BNF.hungriaMendes2015)
  Attribution.externalSourceOwner

compostNitrogenReview2003 : NitrogenPathwaySource
compostNitrogenReview2003 = nitrogen-pathway-source
  compostNitrogenMineralisation
  "Florian Amlinger; Bettina Götz; Peter Dreher; Jutta Geszti; Christof Weissteiner"
  "Nitrogen in biowaste and yard waste compost: dynamics of mobilisation and availability—a review"
  "European Journal of Soil Biology 39(3):107-116"
  2003
  "DOI 10.1016/S1164-5563(03)00026-8"
  reviewSource
  "Total compost nitrogen and immediately plant-available nitrogen are distinct; availability depends on mineralisation, compost properties, soil and cultivation conditions over time."
  "Does not supply a universal first-year availability fraction for arbitrary compost, soil, climate or crop."
  Attribution.externalSourceOwner

aquaponicNitrogenRecoverySource : NitrogenPathwaySource
aquaponicNitrogenRecoverySource = nitrogen-pathway-source
  aquaponicNitrogenRecovery
  (Aquatic.authorsOrInstitution Aquatic.nutrientRecoveryReview2025)
  (Aquatic.title Aquatic.nutrientRecoveryReview2025)
  (Aquatic.venue Aquatic.nutrientRecoveryReview2025)
  (Aquatic.year Aquatic.nutrientRecoveryReview2025)
  (Aquatic.identifier Aquatic.nutrientRecoveryReview2025)
  existingSourceAtlas
  (Aquatic.boundedReading Aquatic.nutrientRecoveryReview2025)
  (Aquatic.excludedPromotion Aquatic.nutrientRecoveryReview2025)
  (Aquatic.claimOwner Aquatic.nutrientRecoveryReview2025)

knfLocalRecyclingLineage : NitrogenPathwaySource
knfLocalRecyclingLineage = nitrogen-pathway-source
  localNitrogenRecycling
  "KNF source lineage plus DASHI reconstruction; see typed owner"
  "Local material-flow / nutrient-recycling lane"
  "DASHI.Environment.KNFSourceAttributionLineageExact"
  2026
  (KNFAttribution.sourceLocator KNFAttribution.knfPermacultureCrossSourceBridge)
  existingTypedLineage
  "KNF/local material transformations may alter where already-fixed nitrogen resides or how it is recycled; this cross-module recycling interpretation is DASHI-owned."
  "Does not attribute atmospheric nitrogen fixation to KNF by label and does not prove net new nitrogen input, retention, availability or yield."
  Attribution.dashiInferenceOwner

record NitrogenSourceAttributionBoundary : Set where
  constructor nitrogen-source-attribution-boundary
  field
    externalSourceAndDashiComparisonRemainDistinct : Bool
    ammoniaAndCompleteFertiliserRemainDistinct : Bool
    fixationAndRecyclingRemainDistinct : Bool
    totalNitrogenAndPlantAvailableNitrogenRemainDistinct : Bool
    sourceReviewAndLocalCalibrationRemainDistinct : Bool
    missingIdentifierMustNotBeInvented : Bool

canonicalNitrogenSourceAttributionBoundary : NitrogenSourceAttributionBoundary
canonicalNitrogenSourceAttributionBoundary =
  nitrogen-source-attribution-boundary true true true true true true
