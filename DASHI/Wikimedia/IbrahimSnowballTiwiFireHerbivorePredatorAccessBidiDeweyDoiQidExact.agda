module DASHI.Wikimedia.IbrahimSnowballTiwiFireHerbivorePredatorAccessBidiDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiBidiPrimarySourceDoiAttributionLedgerExact as Ledger

------------------------------------------------------------------------
-- TIWI MULTI-DRIVER BIDI SNOWBALL
--
-- Highest-alpha ecology continuation after the direct Tiwi fire->shrub search
-- remained unpaid.  Fire and exotic megaherbivores are retained as distinct
-- upstream drivers of vegetation/access structure; predator occurrence,
-- predator density and predator trail use remain distinct consumers.
------------------------------------------------------------------------

melvilleIslandQid : Identity.ExternalIdentityDemand
melvilleIslandQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "place identity"
  "Melville Island / Yermalner, Northern Territory" Identity.wikidataQid
  (Identity.verified "Q504763" "Wikidata place item inspected 2026-09-11; Australian Melville Island, not Canadian Q134116")

bathurstIslandQid : Identity.ExternalIdentityDemand
bathurstIslandQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "place identity"
  "Bathurst Island, Tiwi Islands, Northern Territory" Identity.wikidataQid
  (Identity.verified "Q810814" "Wikidata place item inspected 2026-09-11")

tiwiIslandsQid : Identity.ExternalIdentityDemand
tiwiIslandsQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "archipelago identity"
  "Tiwi Islands" Identity.wikidataQid
  (Identity.verified "Q1323908" "Wikidata Tiwi Islands item inspected 2026-09-11")

tiwiPeopleQid : Identity.ExternalIdentityDemand
tiwiPeopleQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "people identity"
  "Tiwi people" Identity.wikidataQid
  (Identity.verified "Q2933374" "Wikidata people item inspected 2026-09-11; identity does not create Country authority")

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "taxon identity"
  "Bubalus bubalis / water buffalo" Identity.wikidataQid
  (Identity.verified "Q42710" "Wikidata taxon identity retained from current Tiwi source ledger")

horseQid : Identity.ExternalIdentityDemand
horseQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "taxon identity"
  "Equus caballus / horse" Identity.wikidataQid
  (Identity.verified "Q10758650" "Wikidata taxon identity retained from current Tiwi source ledger")

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "taxon identity"
  "dingo" Identity.wikidataQid
  (Identity.verified "Q38584" "Wikidata taxon identity retained from current Tiwi source ledger")

feralCatQid : Identity.ExternalIdentityDemand
feralCatQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "taxon identity"
  "Felis catus / cat" Identity.wikidataQid
  (Identity.verified "Q146" "Wikidata cat identity; does not itself establish feral status or local population")

understoreyQid : Identity.ExternalIdentityDemand
understoreyQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "vegetation-structure identity"
  "understorey / understory" Identity.wikidataQid
  (Identity.verified "Q422666" "Wikidata understorey concept retained; not a measured shrub-density value")

gameTrailQid : Identity.ExternalIdentityDemand
gameTrailQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver predator-access snowball" "landscape-feature identity"
  "game trail / animal trail" Identity.wikidataQid
  (Identity.unresolved "No safely verified direct Wikidata ecological-feature item promoted; article/media objects are not concept substitutes")

------------------------------------------------------------------------
-- Ibrahim/Dewey/DOI coordinates.  Dewey is navigation only.
------------------------------------------------------------------------

multiDriverSavannaCoordinate : Traversal.DashiKnowledgeCoordinate
multiDriverSavannaCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiFireHerbivorePredatorAccessBidiDeweyDoiQidExact.agda"
  "Tiwi savanna multi-driver disturbance / predator-access consumer"
  "577.4 — grassland/savanna ecology; classification coordinate only"
  "Q1323908; Q504763; Q810814; Q422666"
  "DOI 10.1071/PC20088; DOI 10.1002/ece3.71622"

mammalPredatorCoordinate : Traversal.DashiKnowledgeCoordinate
mammalPredatorCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiFireHerbivorePredatorAccessBidiDeweyDoiQidExact.agda"
  "feral-cat/dingo and mammal population consumer"
  "599 — Mammalia; exact ecological disturbance class remains separate"
  "Q146; Q38584; Q42710; Q10758650"
  "DOI 10.1071/PC20088; DOI 10.1002/ece3.71622"

multiDriverToPredatorEdge : Traversal.DashiFirstLinkEdge
multiDriverToPredatorEdge = Traversal.dashi-first-link-edge
  multiDriverSavannaCoordinate mammalPredatorCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "Fire frequency and exotic-herbivore presence nominate predator-density/access consumers; neither coordinate alone determines the predator response."
  true

------------------------------------------------------------------------
-- Primary sources and exact claim ownership.
------------------------------------------------------------------------

data MultiDriverSourceRole : Set where
  islandContrastCatDensityStudy
  MelvilleTrailPredatorAccessStudy : MultiDriverSourceRole

record MultiDriverPrimarySource : Set where
  constructor multi-driver-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : MultiDriverSourceRole
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open MultiDriverPrimarySource public

daviesTiwiLandRangers2022 : MultiDriverPrimarySource
daviesTiwiLandRangers2022 = multi-driver-primary-source
  "Hugh F. Davies; Tiwi Land Rangers; Matthew W. Rees; Danielle Stokeld; Anna C. Miller; Graeme R. Gillespie; Brett P. Murphy"
  "Variation in feral cat density between two large adjacent islands in Australia's monsoon tropics"
  "Pacific Conservation Biology 28(1):18-24"
  2022
  "DOI 10.1071/PC20088"
  islandContrastCatDensityStudy
  "Primary Tiwi Islands camera-grid study contrasting combinations of fire frequency and feral-herbivore presence; estimated feral-cat density on Melville Island and recorded no cat detections on Bathurst grids."
  "The island contrast does not identify a single causal driver, does not prove herbivore absence caused the cat-density difference, and does not by itself pay fire->understorey or understorey->cat mediation."
  Attribution.externalSourceOwner refl

neaveTiwiRangers2025 : MultiDriverPrimarySource
neaveTiwiRangers2025 = multi-driver-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776"
  MelvilleTrailPredatorAccessStudy
  "Primary Melville Island paired-camera study at 52 sites comparing megaherbivore game trails with adjacent undisturbed vegetation; predator detections were much higher on trails, including approximately six-fold higher cat detection and approximately thirty-four-fold higher dingo detection."
  "Trail use is not predation mortality; megaherbivore control is not thereby proved to improve native-mammal demography; Tiwi Rangers collective authorship is retained without converting authorship into universal Country authority."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- BIDI representation: forward drivers and backward consumer constraints.
------------------------------------------------------------------------

data UpstreamDriver : Set where
  fireFrequency
  fireSeverity
  exoticHerbivorePresence
  megaherbivoreTrailFormation
  rainfallContext : UpstreamDriver

data StructuralConsumer : Set where
  shrubDensity
  grassyUnderstorey
  trailMicrocorridor
  coverComplexity : StructuralConsumer

data PredatorConsumer : Set where
  catDetection
  catDensity
  catTrailUse
  dingoDetection
  dingoTrailUse : PredatorConsumer

record MultiDriverBidiFrontier : Set where
  constructor multi-driver-bidi-frontier
  field
    fireFrequencyAcquired : Bool
    herbivorePresenceAcquired : Bool
    shrubUnderstoreyAcquired : Bool
    islandContrastCatDensityAcquired : Bool
    trailPredatorAccessAcquired : Bool
    exactFireToShrubTiwiPaid : Bool
    exactHerbivoreToShrubTiwiPaid : Bool
    shrubToCatDensityPaid : Bool
    trailToCatAccessPaid : Bool
    trailToDingoAccessPaid : Bool
    predatorAccessToPredationMortalityPaid : Bool
    predationToTaxonDemographyPaid : Bool
    completeMultiDriverMediationPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open MultiDriverBidiFrontier public

canonicalMultiDriverBidiFrontier : MultiDriverBidiFrontier
canonicalMultiDriverBidiFrontier = multi-driver-bidi-frontier
  true true true true true
  false false false true true false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Reverse constraints / no-go results.
------------------------------------------------------------------------

data CatDensityIdentifiesFireEffect : Set where
data CatDensityIdentifiesHerbivoreEffect : Set where
data TrailUseMeansPredationMortality : Set where
data HerbivoreControlMeansNativeMammalBenefit : Set where
data IslandContrastMeansCausalIdentification : Set where
data UnderstoreyQidMeansMeasuredUnderstorey : Set where
data TaxonQidMeansLocalPopulation : Set where
data SourceCompletenessMeansMediation : Set where

data SameCatDensityImpliesSameDriverState : Set where

catDensityDoesNotIdentifyFireEffect : CatDensityIdentifiesFireEffect → ⊥
catDensityDoesNotIdentifyFireEffect ()

catDensityDoesNotIdentifyHerbivoreEffect : CatDensityIdentifiesHerbivoreEffect → ⊥
catDensityDoesNotIdentifyHerbivoreEffect ()

trailUseDoesNotMeanPredationMortality : TrailUseMeansPredationMortality → ⊥
trailUseDoesNotMeanPredationMortality ()

herbivoreControlDoesNotMeanNativeMammalBenefit : HerbivoreControlMeansNativeMammalBenefit → ⊥
herbivoreControlDoesNotMeanNativeMammalBenefit ()

islandContrastDoesNotMeanCausalIdentification : IslandContrastMeansCausalIdentification → ⊥
islandContrastDoesNotMeanCausalIdentification ()

understoreyQidDoesNotMeanMeasurement : UnderstoreyQidMeansMeasuredUnderstorey → ⊥
understoreyQidDoesNotMeanMeasurement ()

taxonQidDoesNotMeanLocalPopulation : TaxonQidMeansLocalPopulation → ⊥
taxonQidDoesNotMeanLocalPopulation ()

sourceCompletenessDoesNotMeanMediation : SourceCompletenessMeansMediation → ⊥
sourceCompletenessDoesNotMeanMediation ()

sameCatDensityDoesNotIdentifyDriverState : SameCatDensityImpliesSameDriverState → ⊥
sameCatDensityDoesNotIdentifyDriverState ()

------------------------------------------------------------------------
-- Snowball acquisition/payment: evidence can arrive sideways, payment cannot.
------------------------------------------------------------------------

record MultiDriverAcquisitionState : Set where
  constructor multi-driver-acquisition-state
  field
    MelvilleQidAcquired : Bool
    BathurstQidAcquired : Bool
    TiwiPeopleQidAcquired : Bool
    buffaloQidAcquired : Bool
    horseQidAcquired : Bool
    catQidAcquired : Bool
    dingoQidAcquired : Bool
    understoreyQidAcquired : Bool
    gameTrailQidResolved : Bool
    DaviesPrimaryAcquired : Bool
    NeavePrimaryAcquired : Bool
    fireHistoryAcquired : Bool
    herbivorePresenceAcquired : Bool
    predatorDensityAcquired : Bool
    predatorTrailUseAcquired : Bool
    laterEvidenceRetainedOutOfOrder : Bool

record MultiDriverPaymentState : Set where
  constructor multi-driver-payment-state
  field
    identityCoordinatesPaid : Bool
    primarySourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSitePaid : Bool
    exactTimePaid : Bool
    exactFireStatePaid : Bool
    exactHerbivoreStatePaid : Bool
    exactUnderstoreyStatePaid : Bool
    fireToUnderstoreyPaid : Bool
    herbivoreToUnderstoreyPaid : Bool
    understoreyToCatPaid : Bool
    trailToPredatorAccessPaid : Bool
    predatorAccessToPredationPaid : Bool
    predationToDemographyPaid : Bool
    sameObjectCompositionPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

snowballAcquisitionDoesNotAdvanceMultiDriverPayment :
  MultiDriverAcquisitionState → MultiDriverPaymentState → MultiDriverPaymentState
snowballAcquisitionDoesNotAdvanceMultiDriverPayment _ payment = payment

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator =
  "Direct Tiwi/Melville fire-treatment or herbivore-manipulation -> measured shrub/understorey structural response on a carrier joinable to predator/taxon observations"

firstUnpaidCompositionDiscriminator : String
firstUnpaidCompositionDiscriminator =
  "Same-object separation and composition of fire and exotic-herbivore effects through understorey/trail structure into predator access and taxon demography"

ledgerBoundary : Ledger.TiwiBidiSourceCoverageReceipt
ledgerBoundary = Ledger.canonicalTiwiBidiSourceCoverageReceipt

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
