module DASHI.Wikimedia.IbrahimSnowballTiwi82SiteCovariateVectorDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwi88SitePairwiseJoinDeweyDoiQidExact as Pairwise

------------------------------------------------------------------------
-- TIWI 82-SITE COVARIATE VECTOR
--
-- Penton et al. 2021 explicitly reuses the 2015 88-site Melville camera
-- network, then excludes the six sites that could not be revisited in 2017.
-- On the remaining 82-site carrier, the analysis retains fire frequency,
-- large-feral-herbivore presence, cat activity, shrub density and mammal
-- response variables together.  This pays co-observation / compatible site
-- indexing, not causal mediation among those coordinates.
------------------------------------------------------------------------

understoreyQid : Identity.ExternalIdentityDemand
understoreyQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "vegetation-structure identity"
  "understorey / understory" Identity.wikidataQid
  (Identity.verified "Q422666" "Wikidata understorey concept retained; does not create a site-level shrub-density measurement")

herbivoryQid : Identity.ExternalIdentityDemand
herbivoryQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "ecological-process identity"
  "herbivory" Identity.wikidataQid
  (Identity.verified "Q45874067" "Wikidata herbivory concept retained; does not create Melville feral-herbivore presence or intensity")

catQid : Identity.ExternalIdentityDemand
catQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "taxon identity"
  "Felis catus / cat" Identity.wikidataQid
  (Identity.verified "Q146" "Wikidata cat identity retained; local feral-cat activity requires empirical source")

rabbitRatQid : Identity.ExternalIdentityDemand
rabbitRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "taxon identity"
  "Conilurus penicillatus / brush-tailed rabbit-rat" Identity.wikidataQid
  (Identity.verified "Q303877" "Wikidata taxon identity retained from Tiwi mammal snowball")

blackFootedTreeRatQid : Identity.ExternalIdentityDemand
blackFootedTreeRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "taxon identity"
  "Mesembriomys gouldii / black-footed tree-rat" Identity.wikidataQid
  (Identity.verified "Q1763261" "Wikidata taxon identity retained from Tiwi mammal snowball")

brushtailPossumQid : Identity.ExternalIdentityDemand
brushtailPossumQid = Identity.mkOptionalIdentityDemand
  "Tiwi 82-site covariate vector" "taxon identity"
  "Trichosurus vulpecula / common brushtail possum" Identity.wikidataQid
  (Identity.verified "Q732477" "Species-level Wikidata identity; northern subspecies identity remains a separate unresolved fibre")

covariateCoordinate : Traversal.DashiKnowledgeCoordinate
covariateCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwi82SiteCovariateVectorDeweyDoiQidExact.agda"
  "Melville 82-site fire/herbivore/shrub/cat/mammal covariate carrier"
  "577.4 — savanna ecology; 591.7 — animal ecology; 599 — Mammalia; Dewey is navigation only"
  "Q422666; Q45874067; Q146; Q303877; Q1763261; Q732477"
  "DOI 10.3389/fevo.2021.739550; DOI 10.1111/ddi.12522; DOI 10.1071/WR19198"

------------------------------------------------------------------------
-- Primary source / attribution.
------------------------------------------------------------------------

record CovariateVectorPrimarySource : Set where
  constructor covariate-vector-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    carrierStatement : String
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open CovariateVectorPrimarySource public

pentonEtAl2021 : CovariateVectorPrimarySource
pentonEtAl2021 = covariate-vector-primary-source
  "Cara E. Penton; Hugh F. Davies; Ian J. Radford; Leigh-Ann Woolley; Tiwi Land Rangers; Brett P. Murphy"
  "A Hollow Argument: Understory Vegetation and Disturbance Determine Abundance of Hollow-Dependent Mammals in an Australian Tropical Savanna"
  "Frontiers in Ecology and Evolution 9:739550"
  2021
  "DOI 10.3389/fevo.2021.739550"
  "Camera surveys were conducted at 88 Melville sites in 2015; six could not be revisited in 2017, leaving 82 sites. Table 1 retains fire frequency, large-feral-herbivore presence, feral-cat activity, shrub density and mammal-response variables on this 82-site analysis carrier."
  "Pays same-analysis site compatibility and explicit co-observation of the named covariates; raw data are stated to be available from the authors."
  "Co-observation does not identify causal direction, mediation, row-by-row joins to every external paper, or management benefit. Tiwi Land Rangers collective authorship remains exact and does not become universal Country authority."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Exact 82-site vector.
------------------------------------------------------------------------

data Covariate : Set where
  fireFrequency5Year
  largeFeralHerbivorePresence
  feralCatActivity
  shrubDensity
  coarseWoodyDebris
  rainfall
  distanceToWatercourse
  dingoPresence
  largeEucalyptDensity
  hollowDensity
  mammalDetectionHistory : Covariate

record Same82SiteCovariateReceipt : Set where
  constructor same-82-site-covariate-receipt
  field
    original2015CameraNetworkIs88 : Bool
    sixSitesNotRevisited2017 : Bool
    analysisCarrierIs82 : Bool
    fireFrequencyAtCarrier : Bool
    herbivorePresenceAtCarrier : Bool
    catActivityAtCarrier : Bool
    shrubDensityAtCarrier : Bool
    mammalDetectionAtCarrier : Bool
    hollowTreeVariablesAtCarrier : Bool
    sameAnalysisSiteIndexPaid : Bool
    exactPublicRowIdentifiersPaid : Bool
    causalDirectionPaid : Bool
    mediationPaid : Bool

open Same82SiteCovariateReceipt public

canonicalSame82SiteCovariateReceipt : Same82SiteCovariateReceipt
canonicalSame82SiteCovariateReceipt = same-82-site-covariate-receipt
  true true true true true true true true true true
  false false false

------------------------------------------------------------------------
-- BIDI consequence: one scalar disturbance coordinate is structurally too
-- coarse for consumers that separately inspect fire, herbivory, vegetation,
-- predators and species response.
------------------------------------------------------------------------

data DisturbanceScalarRecovers82SiteVector : Set where
data SameSiteCovariatesMeanCausalChain : Set where
data SameAnalysisMeansSameExternalRows : Set where
data DataAvailabilityStatementMeansPublicDatasetLocated : Set where
data QidMeansMeasuredCovariate : Set where
data DeweyMeansEvidence : Set where
data DOISetMeansMediation : Set where

disturbanceScalarDoesNotRecover82SiteVector : DisturbanceScalarRecovers82SiteVector → ⊥
disturbanceScalarDoesNotRecover82SiteVector ()

sameSiteCovariatesDoNotCreateCausalChain : SameSiteCovariatesMeanCausalChain → ⊥
sameSiteCovariatesDoNotCreateCausalChain ()

sameAnalysisDoesNotCreateExternalRowIdentity : SameAnalysisMeansSameExternalRows → ⊥
sameAnalysisDoesNotCreateExternalRowIdentity ()

dataAvailabilityDoesNotMeanPublicDatasetLocated : DataAvailabilityStatementMeansPublicDatasetLocated → ⊥
dataAvailabilityDoesNotMeanPublicDatasetLocated ()

qidDoesNotMeanMeasuredCovariate : QidMeansMeasuredCovariate → ⊥
qidDoesNotMeanMeasuredCovariate ()

deweyDoesNotMeanEvidence : DeweyMeansEvidence → ⊥
deweyDoesNotMeanEvidence ()

doiSetDoesNotMeanMediation : DOISetMeansMediation → ⊥
doiSetDoesNotMeanMediation ()

------------------------------------------------------------------------
-- Snowball state.  The next acquisition is the actual row-key/data object,
-- not another paper merely repeating the same mechanism.
------------------------------------------------------------------------

record CovariateAcquisitionState : Set where
  constructor covariate-acquisition-state
  field
    PentonPrimaryAcquired : Bool
    Table1CovariatesAcquired : Bool
    same82SiteCarrierAcquired : Bool
    dataAvailabilityStatementAcquired : Bool
    rawDatasetLocated : Bool
    explicitSiteIdentifiersLocated : Bool
    externalRowJoinLocated : Bool
    outOfOrderEvidenceRetained : Bool

record CovariatePaymentState : Set where
  constructor covariate-payment-state
  field
    sourceIdentityPaid : Bool
    attributionPaid : Bool
    DOIIdentityPaid : Bool
    QidIdentityPaid : Bool
    DeweyCoordinatePaid : Bool
    same82SiteCarrierPaid : Bool
    covariateCoObservationPaid : Bool
    exactRowKeysPaid : Bool
    crossPaperRowJoinPaid : Bool
    causalMediationPaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceCovariatePayment :
  CovariateAcquisitionState → CovariatePaymentState → CovariatePaymentState
snowballAcquisitionDoesNotAdvanceCovariatePayment _ payment = payment

firstUnpaidGate : String
firstUnpaidGate =
  "Acquire the actual Penton 82-site raw table or explicit site identifiers, then reconcile those keys against Davies 2017 / Davies 2020 before testing any site-level fire/herbivore -> shrub -> cat mediation model"

priorPairwiseBoundary :
  Pairwise.PairwiseJoinAcquisitionState → Pairwise.PairwiseJoinPaymentState → Pairwise.PairwiseJoinPaymentState
priorPairwiseBoundary = Pairwise.snowballAcquisitionDoesNotAdvancePairwiseJoinPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
