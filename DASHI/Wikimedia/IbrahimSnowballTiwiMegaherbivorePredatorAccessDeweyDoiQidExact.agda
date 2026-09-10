module DASHI.Wikimedia.IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact where

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
-- MULTI-DRIVER TIWI LES FOLLOW: megaherbivore disturbance is a second
-- structural route into predator accessibility alongside fire.  This owner
-- keeps DOI/source attribution, Dewey classification and QID identity separate.
------------------------------------------------------------------------

waterBuffaloQid : Identity.ExternalIdentityDemand
waterBuffaloQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "taxon identity"
  "Bubalus bubalis / water buffalo" Identity.wikidataQid
  (Identity.verified "Q42710" "Wikidata taxon identity verified 2026-09-11; identity alone does not establish Melville presence or ecological effect")

horseQid : Identity.ExternalIdentityDemand
horseQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "taxon identity"
  "Equus caballus / domestic or feral horse" Identity.wikidataQid
  (Identity.verified "Q10758650" "Wikidata taxon identity verified 2026-09-11; feral status and local effect require source evidence")

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "taxon identity"
  "dingo" Identity.wikidataQid
  (Identity.unresolved "No direct QID re-promoted here from a secondary lookup; retain prior verified identity rather than inventing a new one")

gameTrailQid : Identity.ExternalIdentityDemand
gameTrailQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "habitat-structure identity"
  "game trail / animal trail" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact Wikidata ecological-feature item located; do not substitute road/path/article items")

savannaEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
savannaEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact.agda"
  "savanna disturbance / predator-access consumer"
  "577.4 — grassland ecology, including savanna ecology"
  "Q42710; Q10758650; unresolved game-trail QID"
  "DOI 10.1002/ece3.71622; DOI 10.1890/06-1599.1"

record MegaherbivorePredatorPrimarySource : Set where
  constructor megaherbivore-predator-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    boundedClaim : String
    excludedPromotion : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open MegaherbivorePredatorPrimarySource public

neaveEtAl2025 : MegaherbivorePredatorPrimarySource
neaveEtAl2025 = megaherbivore-predator-primary-source
  "Georgina Neave; Brett P. Murphy; Tiwi Rangers; Hugh F. Davies"
  "Exotic Megaherbivores as Ecosystem Engineers in Australian Savannas: Do They Facilitate Predator Movement?"
  "Ecology and Evolution 15(7):e71622"
  2025
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776"
  "Melville Island paired-camera study at 52 sites comparing megaherbivore game trails with adjacent undisturbed vegetation; cats and dingoes were detected substantially more often on trails. Tiwi Rangers are named collective authors."
  "Predator detection is not predation mortality; game-trail preference is not native-mammal demographic effect; megaherbivore control is not a proved conservation benefit."
  Attribution.externalSourceOwner refl

pettyEtAl2007 : MegaherbivorePredatorPrimarySource
pettyEtAl2007 = megaherbivore-predator-primary-source
  "Aaron M. Petty; Patricia A. Werner; Caroline E. R. Lehmann; Jan E. Riley; Daniel S. Banfai; Louis P. Elliott"
  "Savanna responses to feral buffalo in Kakadu National Park, Australia"
  "Ecological Monographs 77(3):441-463"
  2007
  "DOI 10.1890/06-1599.1"
  "Northern-Australian historical-ecology evidence that buffalo population expansion/removal altered ground-cover abundance and composition, competitive regimes and fuel loads, with interacting fire-regime consequences and hysteresis."
  "Kakadu historical cascades are a mechanism/context donor, not a Melville same-site receipt and not evidence that buffalo removal restores a prior state."
  Attribution.externalSourceOwner refl

data Driver : Set where
  fireDriver
  megaherbivoreDriver : Driver

data StructuralConsumer : Set where
  groundCover
  shrubUnderstorey
  woodyStructure
  gameTrailNetwork : StructuralConsumer

data PredatorConsumer : Set where
  catDetection
  dingoDetection
  predationMortality : PredatorConsumer

record MultiDriverPredatorAccessFrontier : Set where
  constructor multi-driver-predator-access-frontier
  field
    TiwiGameTrailPredatorAccessAcquired : Bool
    buffaloGroundCoverDonorAcquired : Bool
    fireStructuralEvidenceAcquired : Bool
    MelvilleShrubFaunaEvidenceAcquired : Bool
    fireToShrubTiwiPaid : Bool
    megaherbivoreToTrailMelvillePaid : Bool
    trailToPredatorDetectionMelvillePaid : Bool
    megaherbivoreToGroundCoverMelvillePaid : Bool
    predatorDetectionToMortalityPaid : Bool
    fullMultiDriverMediationPaid : Bool

open MultiDriverPredatorAccessFrontier public

canonicalMultiDriverPredatorAccessFrontier : MultiDriverPredatorAccessFrontier
canonicalMultiDriverPredatorAccessFrontier = multi-driver-predator-access-frontier
  true true true true
  false true true false false false

------------------------------------------------------------------------
-- BIDI interpretation: predator observations constrain what upstream landscape
-- representation must retain.  A fire-only representation cannot recover a
-- megaherbivore-created trail effect, and a megaherbivore-only representation
-- cannot recover fire history.
------------------------------------------------------------------------

data FireOnlyRepresentationRecoversAllPredatorAccess : Set where
data MegaherbivoreOnlyRepresentationRecoversAllPredatorAccess : Set where
data PredatorDetectionMeansPredationMortality : Set where
data BuffaloRemovalRestoresHistoricalState : Set where
data PrimarySourceAdjacencyCreatesMediation : Set where
data QidCreatesLocalPresence : Set where
data DeweyCreatesCausalParent : Set where

fireOnlyDoesNotRecoverAllPredatorAccess : FireOnlyRepresentationRecoversAllPredatorAccess → ⊥
fireOnlyDoesNotRecoverAllPredatorAccess ()

megaherbivoreOnlyDoesNotRecoverAllPredatorAccess : MegaherbivoreOnlyRepresentationRecoversAllPredatorAccess → ⊥
megaherbivoreOnlyDoesNotRecoverAllPredatorAccess ()

predatorDetectionDoesNotMeanMortality : PredatorDetectionMeansPredationMortality → ⊥
predatorDetectionDoesNotMeanMortality ()

buffaloRemovalDoesNotRestoreHistoricalState : BuffaloRemovalRestoresHistoricalState → ⊥
buffaloRemovalDoesNotRestoreHistoricalState ()

primarySourceAdjacencyDoesNotCreateMediation : PrimarySourceAdjacencyCreatesMediation → ⊥
primarySourceAdjacencyDoesNotCreateMediation ()

qidDoesNotCreateLocalPresence : QidCreatesLocalPresence → ⊥
qidDoesNotCreateLocalPresence ()

deweyDoesNotCreateCausalParent : DeweyCreatesCausalParent → ⊥
deweyDoesNotCreateCausalParent ()

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator = Ledger.firstUnpaidEmpiricalDiscriminator

firstUnpaidMultiDriverDiscriminator : String
firstUnpaidMultiDriverDiscriminator =
  "Melville/Tiwi megaherbivore abundance or grazing pressure -> measured ground/shrub structural change on a carrier joinable to predator and native-mammal observations"

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
