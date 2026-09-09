module DASHI.Environment.AquaticLivingInfrastructureSourceRegistryExact where

open import DASHI.Core.Prelude

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- AQUATIC LIVING-INFRASTRUCTURE SOURCE REGISTRY
--
-- Repository rule (Docs/SourceAttributionPolicy.md):
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != DASHI theorem/extension != promotion/adjudication.
--
-- The sources below calibrate bounded engineering / biological claims only.
-- The unified infrastructure fabric, cross-domain adapters, failure surfaces,
-- and no-shortcut theorems are repository-native DASHI constructions.
------------------------------------------------------------------------

data AquaticSourceRole : Set where
  aquaponicsArchitecture
  rasEngineering
  dissolvedOxygenEngineering
  salineAquaponics
  foamFractionation
  bellSiphonHydraulics
  nutrientRecovery
  microalgaeIntegration : AquaticSourceRole

data PublicationForm : Set where
  reviewArticle
  systematicOrCriticalReview
  engineeringTextbookChapter
  controlledEngineeringStudy : PublicationForm

record AquaticSourceReference : Set where
  constructor aquatic-source-reference
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : AquaticSourceRole
    publicationForm : PublicationForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open AquaticSourceReference public

aquaponicsCriticalReview2025 : AquaticSourceReference
aquaponicsCriticalReview2025 = aquatic-source-reference
  "review authors; recover through DOI"
  "Recent Advances in Aquaponic Systems: A Critical Review"
  "Reviews in Aquaculture"
  2025
  "DOI 10.1111/raq.70029"
  aquaponicsArchitecture
  systematicOrCriticalReview
  "Aquaponics couples aquaculture, water treatment / microbial conversion, and hydroponic plant production; water quality, oxygen, nutrient balance, solids handling, grow-bed mode and monitoring are distinct engineering coordinates."
  "Does not prove that a particular aquaponic design is balanced, closed-loop, productive, safe, or locally suitable."
  Attribution.externalSourceOwner

rasStateOfArt2025 : AquaticSourceReference
rasStateOfArt2025 = aquatic-source-reference
  "review authors; recover through DOI"
  "Review of state-of-the-art improvements in recirculating aquaculture systems: Insights into design, operation, and statistical modeling approaches"
  "Aquaculture"
  2025
  "DOI 10.1016/j.aquaculture.2025.742545"
  rasEngineering
  reviewArticle
  "RAS engineering requires explicit water-treatment, solids, nitrogen-compound, hydraulic, operational and monitoring design rather than a bare recirculation label."
  "Does not establish performance of any particular pump, biofilter, stocking density, species assemblage, or control policy."
  Attribution.externalSourceOwner

rasReview2024 : AquaticSourceReference
rasReview2024 = aquatic-source-reference
  "review authors; recover through DOI"
  "Recent Developments in Recirculating Aquaculture Systems: A Review"
  "Aquaculture Research"
  2024
  "DOI 10.1155/are/6096671"
  rasEngineering
  reviewArticle
  "Calibration for RAS water-quality treatment, microbiological processes, sensing and operational technology."
  "Does not convert review-level synthesis into a site-specific engineering guarantee."
  Attribution.externalSourceOwner

dissolvedOxygenReview2026 : AquaticSourceReference
dissolvedOxygenReview2026 = aquatic-source-reference
  "review authors; recover through DOI"
  "Dissolved oxygen in aquaculture ponds: Causal factors, predictive modeling, and intelligent monitoring"
  "Aquacultural Engineering"
  2026
  "DOI 10.1016/j.aquaeng.2025.102634"
  dissolvedOxygenEngineering
  reviewArticle
  "Dissolved oxygen is a dynamic biological and engineering state requiring measurement/monitoring; oxygen state is affected by multiple interacting factors."
  "Does not imply that pump operation, bubbling, nominal aerator rating, or one sensor reading guarantees organism-safe oxygenation."
  Attribution.externalSourceOwner

salineAquaponicsReview2022 : AquaticSourceReference
salineAquaponicsReview2022 = aquatic-source-reference
  "review authors; recover through DOI"
  "Saline aquaponics: A review of challenges, opportunities, components, and system design"
  "Aquaculture"
  2022
  "DOI 10.1016/j.aquaculture.2022.738173"
  salineAquaponics
  reviewArticle
  "Saline/brackish aquaponics requires joint consideration of physicochemical water state and fish, plant and microorganism salinity compatibility."
  "Does not define one universal brackish threshold or establish cross-species compatibility from a salinity label alone."
  Attribution.externalSourceOwner

marineAquaponicsReview2025 : AquaticSourceReference
marineAquaponicsReview2025 = aquatic-source-reference
  "review authors; recover through DOI"
  "Marine aquaponics for arid and coastal resilience: Closing loops in saline food systems"
  "Aquaculture Reports"
  2025
  "DOI 10.1016/j.aqrep.2025.103123"
  salineAquaponics
  reviewArticle
  "Calibration for marine/saline aquaponic system design, water-quality management, nutrient dynamics, species selection and halophyte integration."
  "Does not establish universal resource efficiency, economic viability, or nutrient closure."
  Attribution.externalSourceOwner

proteinSkimmingLekang2019 : AquaticSourceReference
proteinSkimmingLekang2019 = aquatic-source-reference
  "Odd-Ivar Lekang"
  "Protein Skimming, Flotation, Coagulation and Flocculation"
  "Aquaculture Engineering, textbook chapter 7"
  2019
  "DOI 10.1002/9781119489047.ch7"
  foamFractionation
  engineeringTextbookChapter
  "Protein skimming / foam fractionation is a specific gas-liquid separation route used to remove colloidal and dissolved substances; it is distinct from generic mechanical and biological filtration."
  "Does not prove that a skimmer removes every contaminant or that a skimmer is required or sufficient for every aquarium/RAS system."
  Attribution.externalSourceOwner

bellSiphonHydraulics2026 : AquaticSourceReference
bellSiphonHydraulics2026 = aquatic-source-reference
  "study authors; recover through DOI"
  "Effect of standpipe diameter on hydraulic cycling and nutrient-transformation performance in a bell siphon-driven aquaponic recirculating system"
  "Separation and Purification Technology"
  2026
  "DOI 10.1016/j.seppur.2026.139378"
  bellSiphonHydraulics
  controlledEngineeringStudy
  "Bell-siphon standpipe geometry can alter flood-drain timing, discharge behaviour and hydraulic stability in the studied media-bed aquaponic system."
  "Does not make bell siphons pumps, aerators, nutrient-removal devices by definition, nor establish the reported geometry as universal."
  Attribution.externalSourceOwner

nutrientRecoveryReview2025 : AquaticSourceReference
nutrientRecoveryReview2025 = aquatic-source-reference
  "review authors; canonical publisher locator retained"
  "Current technologies for nutrient recovery in aquaponic systems: a review"
  "Frontiers"
  2025
  "Canonical Frontiers article; DOI not asserted here without a verified locator"
  nutrientRecovery
  reviewArticle
  "Nutrient recovery may use physical solids separation, chemical recovery, biological digestion/mineralisation and hybrid pathways."
  "Does not identify nutrient recovery with total nutrient closure or prove one recovery pathway optimal."
  Attribution.externalSourceOwner

microalgaeRASReview2024 : AquaticSourceReference
microalgaeRASReview2024 = aquatic-source-reference
  "review authors; recover through DOI"
  "Review of recirculating aquaculture systems integrated with microalgae"
  "Bioresource Technology"
  2024
  "DOI 10.1016/j.biortech.2024.131107"
  microalgaeIntegration
  reviewArticle
  "Microalgal integration is a candidate biological route for nutrient recovery, carbon uptake and oxygen-related system services in RAS."
  "Does not imply net oxygen sufficiency, net carbon benefit, species compatibility or economic viability in a particular system."
  Attribution.externalSourceOwner

record AquaticAttributionBoundary : Set where
  constructor aquatic-attribution-boundary
  field
    reviewClaimAndDashiTheoremRemainDistinct : Bool
    sourceArchitectureAndImplementationGuaranteeRemainDistinct : Bool
    sourceMechanismAndMeasuredOutcomeRemainDistinct : Bool
    crossSourceSystemSynthesisIsDashiOwned : Bool
    missingMetadataMustNotBeInvented : Bool
    oneSourceAutomaticallyPromotesRecommendation : Bool

canonicalAquaticAttributionBoundary : AquaticAttributionBoundary
canonicalAquaticAttributionBoundary =
  aquatic-attribution-boundary true true true true true false
