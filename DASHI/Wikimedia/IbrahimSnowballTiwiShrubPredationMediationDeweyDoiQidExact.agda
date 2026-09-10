module DASHI.Wikimedia.IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact as Prior

------------------------------------------------------------------------
-- TIWI SHRUB-STRUCTURE / PREDATION MEDIATION SNOWBALL
--
-- LiDAR is deliberately not required here.  This owner follows direct field
-- observations on Melville Island: shrub density, cat detection/activity,
-- fire/disturbance context, and taxon-specific abundance/occupancy.  QID,
-- Dewey and DOI remain identity/classification/provenance coordinates only.
------------------------------------------------------------------------

shrubQid : Identity.ExternalIdentityDemand
shrubQid = Identity.mkOptionalIdentityDemand
  "Tiwi shrub/predation mediation continuation" "external vegetation life-form identity"
  "shrub" Identity.wikidataQid
  (Identity.verified "Q42295" "Wikidata shrub item inspected 2026-09-11; life-form identity is not shrub-density evidence")

shrublandQid : Identity.ExternalIdentityDemand
shrublandQid = Identity.mkOptionalIdentityDemand
  "Tiwi shrub/predation mediation continuation" "external vegetation-formation identity"
  "shrubland" Identity.wikidataQid
  (Identity.verified "Q879641" "Wikidata shrubland item inspected 2026-09-11; vegetation formation is distinct from plot-level shrub density")

brushTailedRabbitRatQid : Identity.ExternalIdentityDemand
brushTailedRabbitRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi shrub/predation mediation continuation" "external taxon identity"
  "Conilurus penicillatus / brush-tailed rabbit-rat" Identity.wikidataQid
  (Identity.verified "Q303877" "Wikidata taxon item inspected 2026-09-11; species identity does not create local abundance or decline evidence")

------------------------------------------------------------------------
-- Ibrahim / Dewey / DOI / QID coordinates.
------------------------------------------------------------------------

savannaUnderstoreyCoordinate : Traversal.DashiKnowledgeCoordinate
savannaUnderstoreyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact.agda"
  "savanna understorey / shrub-structure consumer"
  "577.4 — grassland/savanna ecology; classification coordinate only"
  "Q42295; Q879641"
  "DOI 10.3389/fevo.2021.739550"

rabbitRatPredationCoordinate : Traversal.DashiKnowledgeCoordinate
rabbitRatPredationCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact.agda"
  "brush-tailed rabbit-rat distribution / cat-predation consumer"
  "599 — Mammalia; taxon-specific DDC is not used as causal evidence"
  "Q303877"
  "DOI 10.1111/ddi.12522"

understoreySupportsRabbitRat : Traversal.DashiFirstLinkEdge
understoreySupportsRabbitRat = Traversal.dashi-first-link-edge
  savannaUnderstoreyCoordinate rabbitRatPredationCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "Melville Island field studies associate shrub density, cat activity/detection and brush-tailed rabbit-rat occurrence/abundance; mediation remains study- and consumer-bounded"
  true

------------------------------------------------------------------------
-- Exact source attribution.
------------------------------------------------------------------------

data TiwiMediationSourceRole : Set where
  longTermDistributionPredationStudy
  hollowDependentMammalUnderstoreyStudy
  adjacentIslandPopulationTrajectoryStudy : TiwiMediationSourceRole

record TiwiMediationPrimarySource : Set where
  constructor tiwi-mediation-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : TiwiMediationSourceRole
    collectiveAuthorReference : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open TiwiMediationPrimarySource public

daviesEtAl2017 : TiwiMediationPrimarySource
daviesEtAl2017 = tiwi-mediation-primary-source
  "Hugh F. Davies; Michael A. McCarthy; R. S. C. Firth; John C. Z. Woinarski; Graeme R. Gillespie; Alan N. Andersen; Hayley M. Geyle; Emily Nicholson; Brett P. Murphy"
  "Top-down control of species distributions: feral cats driving the regional extinction of a threatened rodent in northern Australia"
  "Diversity and Distributions 23:272-283"
  2017
  "DOI 10.1111/ddi.12522"
  longTermDistributionPredationStudy
  "No collective Tiwi author is listed on this publication; do not infer authorship from study location or acknowledgments."
  "Primary Melville Island study comparing 2015 surveys at 88 sites with 2000-2002 history; dynamic/single-season occupancy analyses report brush-tailed rabbit-rat restriction to areas with low feral-cat detection and high shrub density, and model local extinction correlates."
  "Observational/dynamic-occupancy evidence does not make shrub density a sole cause, does not establish every fire-to-shrub step experimentally, and does not transfer automatically to other Tiwi taxa or Country."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

pentonEtAl2021 : TiwiMediationPrimarySource
pentonEtAl2021 = tiwi-mediation-primary-source
  "Cara E. Penton; Hugh F. Davies; Ian J. Radford; Leigh-Ann Woolley; Tiwi Land Rangers; Brett P. Murphy"
  "A Hollow Argument: Understory Vegetation and Disturbance Determine Abundance of Hollow-Dependent Mammals in an Australian Tropical Savanna"
  "Frontiers in Ecology and Evolution 9:739550"
  2021
  "DOI 10.3389/fevo.2021.739550"
  hollowDependentMammalUnderstoreyStudy
  "Tiwi Land Rangers are a named collective author. Acknowledged Tiwi Land Council, Traditional Owners, named rangers, Tiwi College staff/students remain distinct attribution roles."
  "Primary Melville Island analysis of brush-tailed rabbit-rat, black-footed tree-rat and northern brushtail possum abundance against tree hollows, large eucalypts, shrub density, cat activity and fire/disturbance variables; shrub density appears in all well-supported species models with species-specific directions."
  "No universal hollow-irrelevance theorem, no claim that shrub density alone is causal, and no assumption that one species' sign or response transfers to another."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

neaveEtAl2024 : TiwiMediationPrimarySource
neaveEtAl2024 = tiwi-mediation-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Alan N. Andersen; Hugh F. Davies"
  "The intact and the imperilled: contrasting mammal population trajectories between two large adjacent islands"
  "Wildlife Research 51:WR24039"
  2024
  "DOI 10.1071/WR24039"
  adjacentIslandPopulationTrajectoryStudy
  "Tiwi Rangers are a named collective author; collective authorship does not identify every individual ranger or create whole-Country authority."
  "Primary Tiwi Islands comparison of mammal trajectories and contrasting disturbance/predator contexts between Bathurst and Melville Islands; retained as a broad same-archipelago context source, not a substitute for plot-level mediation."
  "Island contrast does not by itself identify the causal contribution of fire, cats, herbivores, rainfall or vegetation structure and does not replace Davies/Penton site-level evidence."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Consumer-specific empirical state.
------------------------------------------------------------------------

record TiwiShrubPredationEvidenceCell : Set where
  constructor tiwi-shrub-predation-evidence-cell
  field
    source : TiwiMediationPrimarySource
    exactIsland : String
    exactSiteOrPlot : String
    exactMeasurementWindow : String
    taxonReference : String
    shrubDensityReference : String
    fireHistoryReference : String
    catDetectionOrActivityReference : String
    abundanceOrOccupancyReference : String
    modelOrDesignReference : String
    uncertaintyReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open TiwiShrubPredationEvidenceCell public

record TiwiShrubPredationMediationFrontier : Set where
  constructor tiwi-shrub-predation-mediation-frontier
  field
    MelvilleRabbitRatHistoryAcquired : Bool
    shrubDensityEvidenceAcquired : Bool
    catDetectionEvidenceAcquired : Bool
    taxonAbundanceEvidenceAcquired : Bool
    multiTaxonUnderstoreyEvidenceAcquired : Bool
    namedTiwiCollectiveAuthorshipRetained : Bool
    exactFireToShrubCausalStepPaid : Bool
    exactShrubToCatAccessStepPaid : Bool
    exactCatToRabbitRatDemographyPaid : Bool
    completeFireShrubCatTaxonMediationPaid : Bool
    crossTaxonTransportPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiShrubPredationMediationFrontier public

canonicalTiwiShrubPredationMediationFrontier : TiwiShrubPredationMediationFrontier
canonicalTiwiShrubPredationMediationFrontier = tiwi-shrub-predation-mediation-frontier
  true true true true true true
  false false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Snowball acquisition/payment separation.
------------------------------------------------------------------------

record TiwiShrubPredationAcquisitionState : Set where
  constructor tiwi-shrub-predation-acquisition-state
  field
    shrubQidAcquired : Bool
    shrublandQidAcquired : Bool
    rabbitRatQidAcquired : Bool
    deweyCoordinateAcquired : Bool
    Davies2017Acquired : Bool
    Penton2021Acquired : Bool
    Neave2024Acquired : Bool
    exactSourceAttributionAcquired : Bool
    shrubMeasurementsAcquired : Bool
    fireMeasurementsAcquired : Bool
    catMeasurementsAcquired : Bool
    taxonMeasurementsAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiShrubPredationAcquisitionState public

record TiwiShrubPredationPaymentState : Set where
  constructor tiwi-shrub-predation-payment-state
  field
    qidIdentityPaid : Bool
    deweyClassificationPaid : Bool
    doiSourceIdentityPaid : Bool
    exactSourceAttributionPaid : Bool
    collectiveAuthorRolePaid : Bool
    exactIslandPaid : Bool
    exactSitePaid : Bool
    exactTimePaid : Bool
    exactTaxonPaid : Bool
    shrubDensityConsumerPaid : Bool
    catDetectionConsumerPaid : Bool
    abundanceOccupancyConsumerPaid : Bool
    fireHistoryConsumerPaid : Bool
    fireToShrubCausalPaid : Bool
    shrubToPredatorAccessPaid : Bool
    predatorToDemographyPaid : Bool
    jointMediationPaid : Bool
    crossTaxonTransportPaid : Bool
    CountryAuthorityRetained : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiShrubPredationPaymentState public

snowballAcquisitionDoesNotAdvanceTiwiShrubPredationPayment :
  TiwiShrubPredationAcquisitionState → TiwiShrubPredationPaymentState → TiwiShrubPredationPaymentState
snowballAcquisitionDoesNotAdvanceTiwiShrubPredationPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data ShrubQidMeansShrubDensity : Set where
data ShrublandMeansPlotShrubDensity : Set where
data RabbitRatQidMeansLocalPopulation : Set where
data HighShrubDensityMeansNoCats : Set where
data LowCatDetectionMeansNoPredation : Set where
data CorrelationMeansCompleteMediation : Set where
data HollowDependenceMeansHollowAvailabilityLimitsPopulation : Set where
data OneTaxonResponseMeansAllTaxaSameSign : Set where
data CollectiveAuthorshipMeansCountryAuthority : Set where
data CountryAuthorityMeansEcologicalEffect : Set where
data DeweyMeansSemanticParent : Set where
data DOIIdentifiesConcept : Set where
data AcquisitionCreatesPayment : Set where

shrubQidDoesNotCreateShrubDensity : ShrubQidMeansShrubDensity → ⊥
shrubQidDoesNotCreateShrubDensity ()

shrublandDoesNotCreatePlotShrubDensity : ShrublandMeansPlotShrubDensity → ⊥
shrublandDoesNotCreatePlotShrubDensity ()

rabbitRatQidDoesNotCreateLocalPopulation : RabbitRatQidMeansLocalPopulation → ⊥
rabbitRatQidDoesNotCreateLocalPopulation ()

highShrubDensityDoesNotMeanNoCats : HighShrubDensityMeansNoCats → ⊥
highShrubDensityDoesNotMeanNoCats ()

lowCatDetectionDoesNotMeanNoPredation : LowCatDetectionMeansNoPredation → ⊥
lowCatDetectionDoesNotMeanNoPredation ()

correlationDoesNotCreateCompleteMediation : CorrelationMeansCompleteMediation → ⊥
correlationDoesNotCreateCompleteMediation ()

hollowDependenceDoesNotMeanHollowLimitation : HollowDependenceMeansHollowAvailabilityLimitsPopulation → ⊥
hollowDependenceDoesNotMeanHollowLimitation ()

oneTaxonResponseDoesNotTransportSign : OneTaxonResponseMeansAllTaxaSameSign → ⊥
oneTaxonResponseDoesNotTransportSign ()

collectiveAuthorshipDoesNotCreateCountryAuthority : CollectiveAuthorshipMeansCountryAuthority → ⊥
collectiveAuthorshipDoesNotCreateCountryAuthority ()

countryAuthorityDoesNotCreateEcologicalEffect : CountryAuthorityMeansEcologicalEffect → ⊥
countryAuthorityDoesNotCreateEcologicalEffect ()

deweyDoesNotCreateSemanticParent : DeweyMeansSemanticParent → ⊥
deweyDoesNotCreateSemanticParent ()

doiDoesNotIdentifyConcept : DOIIdentifiesConcept → ⊥
doiDoesNotIdentifyConcept ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

------------------------------------------------------------------------
-- Reuse canonical prior boundaries.
------------------------------------------------------------------------

priorPredationSnowball :
  Prior.PredationHabitatAcquisitionState → Prior.PredationHabitatPaymentState → Prior.PredationHabitatPaymentState
priorPredationSnowball = Prior.snowballAcquisitionDoesNotAdvancePredationHabitatPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
