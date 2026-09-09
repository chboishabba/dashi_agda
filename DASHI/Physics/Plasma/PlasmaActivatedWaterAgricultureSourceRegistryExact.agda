module DASHI.Physics.Plasma.PlasmaActivatedWaterAgricultureSourceRegistryExact where

open import DASHI.Core.Prelude

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PLASMA-ACTIVATED / PLASMA-TREATED WATER SOURCE REGISTRY
--
-- Repository attribution rule (Docs/SourceAttributionPolicy.md):
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != DASHI theorem/extension != recommendation.
--
-- This owner only records bounded source claims about plasma-liquid chemistry
-- and agricultural use.  No source below is promoted to a universal statement
-- that "plasma-touched water is fertiliser" independent of discharge, gas,
-- water composition, dose, storage, crop, soil/root-zone state or comparator.
------------------------------------------------------------------------

data PAWSourceRole : Set where
  plasmaLiquidChemistry
  reactiveNitrogenChemistry
  nitrogenFertiliserDeviceReview
  agricultureApplicationReview
  agricultureMetaAnalysis : PAWSourceRole

data PAWPublicationForm : Set where
  focusedReview
  stateOfArtReview
  deviceReview
  metaAnalysis : PAWPublicationForm

record PAWSourceReference : Set where
  constructor paw-source-reference
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : PAWSourceRole
    publicationForm : PAWPublicationForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open PAWSourceReference public

bruggemanRNS2020 : PAWSourceReference
bruggemanRNS2020 = paw-source-reference
  "authors recoverable through DOI"
  "Reactive nitrogen species in plasma-activated water: generation, chemistry and application in agriculture"
  "Journal of Physics D: Applied Physics"
  2020
  "DOI 10.1088/1361-6463/ab795a"
  reactiveNitrogenChemistry
  focusedReview
  "Non-thermal plasma can generate reactive nitrogen species in treated water; long-lived nitrite and nitrate and shorter-lived species depend strongly on discharge type, gas composition, liquid properties and treatment conditions."
  "Does not establish one fixed PAW composition, universal agronomic benefit, safe dose, or equivalence between nitrate concentration and complete fertiliser value."
  Attribution.externalSourceOwner

puač2025 : PAWSourceReference
puač2025 = paw-source-reference
  "Puač et al.; full author list recoverable through DOI"
  "Plasma-Liquid Interaction for Agriculture—A Focused Review"
  "Plasma Processes and Polymers"
  2025
  "DOI 10.1002/ppap.202400208"
  plasmaLiquidChemistry
  focusedReview
  "Reviews plasma-activated water chemistry in agriculture, including formation of nitrate, nitrite and hydrogen peroxide, discharge diversity and plant-facing applications."
  "Does not promote reactive-species presence to plant benefit without composition, application and biological context."
  Attribution.externalSourceOwner

robinsonStapelmann2024 : PAWSourceReference
robinsonStapelmann2024 = paw-source-reference
  "C. Robinson; K. Stapelmann"
  "Plasma treating water for nitrate based nitrogen fertilizer - A review of recent device designs"
  "Current Opinion in Green and Sustainable Chemistry"
  2024
  "DOI 10.1016/j.cogsc.2024.100978"
  nitrogenFertiliserDeviceReview
  deviceReview
  "Atmospheric-pressure air plasma treatment can fix nitrogen into water, with nitrate a major long-lived product in oxygen-containing air-plasma systems; the review evaluates device designs for nitrogen-fertiliser production."
  "Does not establish energy competitiveness, agronomic equivalence to a complete fertiliser, or suitability of every plasma-treated water batch."
  Attribution.externalSourceOwner

guo2021 : PAWSourceReference
guo2021 = paw-source-reference
  "Guo, Liu, Zhou, Xie, He"
  "Plasma-activated water production and its application in agriculture"
  "Journal of the Science of Food and Agriculture"
  2021
  "DOI 10.1002/jsfa.11258"
  agricultureApplicationReview
  focusedReview
  "Reviews PAW production parameters and reported agricultural applications including seed germination, plant growth and disease/pest-related uses."
  "Does not identify review-level application reports with a universal causal effect or recommendation."
  Attribution.externalSourceOwner

longEtAl2026 : PAWSourceReference
longEtAl2026 = paw-source-reference
  "Nguyen Van Duc Long; Sourjo Sengupta; Changping Zhuang; Katharina Richter; Volker Hessel"
  "Plasma-activated water in agriculture, food safety, and healthcare"
  "Chemical Engineering Journal"
  2026
  "DOI 10.1016/j.cej.2025.172535"
  agricultureApplicationReview
  stateOfArtReview
  "State-of-the-art review of PAW chemistry, reactive species, applications and remaining industrial/regulatory challenges."
  "Does not establish that PAW is compositionally stable, safe, effective or regulatory-admissible for an unspecified use."
  Attribution.externalSourceOwner

frontiersMeta2026 : PAWSourceReference
frontiersMeta2026 = paw-source-reference
  "meta-analysis authors recoverable through DOI"
  "Global meta-analysis of plasma-activated water for improving crop establishment, productivity, and health"
  "Frontiers in Plant Science"
  2026
  "DOI 10.3389/fpls.2026.1754073"
  agricultureMetaAnalysis
  metaAnalysis
  "Meta-analysis reports pooled positive responses across several plant outcomes and reports PAW-associated changes in pH, conductivity, nitrate, nitrite, hydrogen peroxide and oxidation-reduction potential."
  "Does not erase study heterogeneity or determine the effect of a particular reactor, water chemistry, crop, dose, application route or site."
  Attribution.externalSourceOwner

record PAWAttributionBoundary : Set where
  constructor paw-attribution-boundary
  field
    plasmaExposureAndMeasuredCompositionRemainDistinct : Bool
    reactiveNitrogenPresenceAndCompleteFertiliserRemainDistinct : Bool
    reviewFindingAndDashiTheoremRemainDistinct : Bool
    metaAnalyticEffectAndSiteRecommendationRemainDistinct : Bool
    chemistrySourceAndAgronomicOutcomeSourceRemainDistinct : Bool
    missingMetadataMustNotBeInvented : Bool
    plasmaTouchedWaterAutomaticallyMeansFertiliser : Bool

canonicalPAWAttributionBoundary : PAWAttributionBoundary
canonicalPAWAttributionBoundary =
  paw-attribution-boundary true true true true true true false
