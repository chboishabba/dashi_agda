module DASHI.Wikimedia.IbrahimSnowballTiwiMultiDriverUnderstoreyPredatorBidiExact where

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
-- TIWI MULTI-DRIVER UNDERSTOREY -> PREDATOR BIDI SNOWBALL
--
-- The active LES object is no longer fire-only.  Fire history and exotic
-- megaherbivore disturbance are retained as separate upstream fibres that may
-- both alter vegetation/access structure before predator and prey consumers.
-- No cross-source composition is attributed back to an external paper.
------------------------------------------------------------------------

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver LES" "external taxon identity" "Bubalus bubalis"
  Identity.wikidataQid
  (Identity.verified "Q42710" "Wikidata water-buffalo taxon inspected 2026-09-11; taxon identity does not establish Melville abundance or ecological effect")

horseQid : Identity.ExternalIdentityDemand
horseQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver LES" "external taxon identity" "Equus caballus"
  Identity.wikidataQid
  (Identity.verified "Q10758650" "Wikidata Equus caballus taxon inspected 2026-09-11; synonym/taxon-history variants do not alter the empirical carrier")

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver LES" "external predator identity" "dingo"
  Identity.wikidataQid
  (Identity.verified "Q38584" "Wikidata dingo item inspected 2026-09-11; taxonomy is disputed and QID identity does not create a predation observation")

gameTrailQid : Identity.ExternalIdentityDemand
gameTrailQid = Identity.mkOptionalIdentityDemand
  "Tiwi multi-driver LES" "external habitat-feature identity" "game trail / animal trail"
  Identity.wikidataQid
  (Identity.unresolved "No safely verified exact ecological game-trail concept QID promoted in this tranche")

multiDriverCoordinate : Traversal.DashiKnowledgeCoordinate
multiDriverCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMultiDriverUnderstoreyPredatorBidiExact.agda"
  "Tiwi multi-driver savanna disturbance"
  "577.4 — grassland/savanna ecology consumer coordinate"
  "Q42710; Q10758650; Q38584; game-trail QID unresolved"
  "DOI 10.1071/PC20088; DOI 10.1002/ece3.71622"

------------------------------------------------------------------------
-- Primary source carriers.
------------------------------------------------------------------------

data MultiDriverSourceRole : Set where
  islandCatDensityFireHerbivoreComparison
  gameTrailPredatorAccessPairedCameraStudy : MultiDriverSourceRole

record MultiDriverPrimarySource : Set where
  constructor multi-driver-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : MultiDriverSourceRole
    carrier : String
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open MultiDriverPrimarySource public

daviesTiwiLandRangersEtAl2022 : MultiDriverPrimarySource
daviesTiwiLandRangersEtAl2022 = multi-driver-primary-source
  "Hugh F. Davies; Tiwi Land Rangers; Matthew W. Rees; Danielle Stokeld; Anna C. Miller; Graeme R. Gillespie; Brett P. Murphy"
  "Variation in feral cat density between two large adjacent islands in Australia's monsoon tropics"
  "Pacific Conservation Biology 28(1):18-24"
  2022
  "DOI 10.1071/PC20088"
  islandCatDensityFireHerbivoreComparison
  "Melville Island and Bathurst Island; four approximately 13-km2 camera grids under differing fire-frequency / feral-herbivore contexts"
  "Primary island-comparison evidence: estimated feral-cat density on Melville and no cat detections in the Bathurst sampling; authors identify absence of feral herbivores on Bathurst as a possible contributor rather than a demonstrated isolated cause."
  "Does not identify herbivore -> understorey -> cat-density mediation, does not isolate fire from herbivores, and management language does not constitute an intervention outcome."
  Attribution.externalSourceOwner refl

neaveMurphyTiwiRangersDavies2025 : MultiDriverPrimarySource
neaveMurphyTiwiRangersDavies2025 = multi-driver-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776"
  gameTrailPredatorAccessPairedCameraStudy
  "52 Melville Island savanna sites in 2022; paired cameras on megaherbivore game trails and adjacent undisturbed vegetation"
  "Primary same-site paired evidence that dingoes and feral cats were detected substantially more often on megaherbivore game trails than adjacent vegetation; native-mammal trail responses differed by taxon and vegetation density."
  "Game-trail detection does not equal predation mortality; megaherbivore control does not automatically create native-mammal benefit; game trails are not equivalent to fire-created open habitat."
  Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- BIDI decomposition: two upstream disturbance fibres remain independent.
------------------------------------------------------------------------

data DisturbanceDriver : Set where
  fireRegime
  megaherbivorePressure
  plantationConversion
  rainfallContext : DisturbanceDriver

data StructuralConsumer : Set where
  shrubDensity
  groundLayerDensity
  woodySizeStructure
  gameTrailAvailability
  openMovementCorridor : StructuralConsumer

data PredatorConsumer : Set where
  catDensity
  catDetection
  dingoDetection
  predatorTrailUse : PredatorConsumer

data FaunaConsumer : Set where
  taxonAbundance
  taxonOccupancy
  taxonConnectivity
  taxonPredationMortality : FaunaConsumer

record TiwiMultiDriverBidiFrontier : Set where
  constructor tiwi-multi-driver-bidi-frontier
  field
    fireIsSeparateDriver : Bool
    megaherbivoreIsSeparateDriver : Bool
    plantationIsSeparateDriver : Bool
    rainfallIsSeparateDriver : Bool
    MelvilleCatDensityPrimaryPaid : Bool
    BathurstMelvilleContrastPaid : Bool
    MelvilleGameTrailPredatorAccessPaid : Bool
    TiwiUnderstoreyFaunaAssociationPaid : Bool
    exactFireToShrubPaid : Bool
    exactHerbivoreToShrubPaid : Bool
    exactHerbivoreToTrailPaid : Bool
    trailToPredatorDetectionPaid : Bool
    predatorDetectionToPredationPaid : Bool
    predationToTaxonDemographyPaid : Bool
    fullFirePathPaid : Bool
    fullHerbivorePathPaid : Bool
    jointDriverInteractionPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsCrossSourceInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiMultiDriverBidiFrontier public

canonicalTiwiMultiDriverBidiFrontier : TiwiMultiDriverBidiFrontier
canonicalTiwiMultiDriverBidiFrontier = tiwi-multi-driver-bidi-frontier
  true true true true
  true true true true
  false false true true
  false false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Reverse constraints: predator occurrence/detection does not identify which
-- upstream disturbance driver generated the accessible habitat state.
------------------------------------------------------------------------

data SamePredatorSignalMeansSameDriver : Set where
data SameUnderstoreyMeansSameHistory : Set where
data IslandContrastMeansHerbivoreCausality : Set where
data GameTrailUseMeansPredationMortality : Set where
data HerbivoreControlMeansNativeBenefit : Set where
data FireAndHerbivoreMayBeCollapsed : Set where
data QidCreatesDriverEffect : Set where
data PrimarySourceAdjacencyCreatesJointMediation : Set where

samePredatorSignalDoesNotIdentifyDriver : SamePredatorSignalMeansSameDriver → ⊥
samePredatorSignalDoesNotIdentifyDriver ()

sameUnderstoreyDoesNotIdentifyHistory : SameUnderstoreyMeansSameHistory → ⊥
sameUnderstoreyDoesNotIdentifyHistory ()

islandContrastDoesNotCreateHerbivoreCausality : IslandContrastMeansHerbivoreCausality → ⊥
islandContrastDoesNotCreateHerbivoreCausality ()

gameTrailUseDoesNotCreatePredationMortality : GameTrailUseMeansPredationMortality → ⊥
gameTrailUseDoesNotCreatePredationMortality ()

herbivoreControlDoesNotCreateNativeBenefit : HerbivoreControlMeansNativeBenefit → ⊥
herbivoreControlDoesNotCreateNativeBenefit ()

fireAndHerbivoreDoNotCollapse : FireAndHerbivoreMayBeCollapsed → ⊥
fireAndHerbivoreDoNotCollapse ()

qidDoesNotCreateDriverEffect : QidCreatesDriverEffect → ⊥
qidDoesNotCreateDriverEffect ()

primarySourceAdjacencyDoesNotCreateJointMediation : PrimarySourceAdjacencyCreatesJointMediation → ⊥
primarySourceAdjacencyDoesNotCreateJointMediation ()

------------------------------------------------------------------------
-- Snowball acquisition/payment: new middle-layer evidence can be retained
-- without moving the still-first Tiwi fire -> shrub payment gate.
------------------------------------------------------------------------

record MultiDriverAcquisitionState : Set where
  constructor multi-driver-acquisition-state
  field
    buffaloQidAcquired : Bool
    horseQidAcquired : Bool
    dingoQidAcquired : Bool
    gameTrailQidResolved : Bool
    Davies2022PrimaryAcquired : Bool
    Neave2025PrimaryAcquired : Bool
    pairedCameraDatasetAcquired : Bool
    fireContextAcquired : Bool
    herbivoreContextAcquired : Bool
    understoreyContextAcquired : Bool
    predatorContextAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open MultiDriverAcquisitionState public

record MultiDriverPaymentState : Set where
  constructor multi-driver-payment-state
  field
    taxonIdentityPaid : Bool
    sourceIdentityPaid : Bool
    sourceRolePaid : Bool
    carrierPaid : Bool
    fireToShrubPaid : Bool
    herbivoreToShrubPaid : Bool
    herbivoreToTrailPaid : Bool
    trailToPredatorPaid : Bool
    predatorToMortalityPaid : Bool
    mortalityToDemographyPaid : Bool
    sameSiteTimePaid : Bool
    interactionPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open MultiDriverPaymentState public

snowballAcquisitionDoesNotAdvanceMultiDriverPayment :
  MultiDriverAcquisitionState → MultiDriverPaymentState → MultiDriverPaymentState
snowballAcquisitionDoesNotAdvanceMultiDriverPayment _ payment = payment

canonicalFirstUnpaidGate : String
canonicalFirstUnpaidGate =
  "Exact Tiwi/Melville fire treatment -> measured shrub/understorey density on a carrier joinable to the mammal/predator observations; herbivore->shrub remains a separate unpaid sibling gate"

sourceLedgerBoundary : Ledger.TiwiBidiSourceCoverageReceipt
sourceLedgerBoundary = Ledger.canonicalTiwiBidiSourceCoverageReceipt

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
