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

pigQid : Identity.ExternalIdentityDemand
pigQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "taxon identity"
  "Sus scrofa / pig / wild boar" Identity.wikidataQid
  (Identity.verified "Q58697" "Wikidata Sus scrofa taxon identity verified 2026-09-11; Neave records pigs as contextual Melville presence, not as a measured game-trail driver in the paired-camera contrast")

herbivoryQid : Identity.ExternalIdentityDemand
herbivoryQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "ecological-process identity"
  "herbivory" Identity.wikidataQid
  (Identity.verified "Q45874067" "Wikidata herbivory concept verified 2026-09-11; concept identity does not quantify local grazing pressure")

ecologicalDisturbanceQid : Identity.ExternalIdentityDemand
ecologicalDisturbanceQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "ecological-process identity"
  "ecological disturbance" Identity.wikidataQid
  (Identity.verified "Q966490" "Wikidata ecological-disturbance concept directly inspected 2026-09-11; concept identity does not establish a local disturbance effect")

ecologicalConnectivityQid : Identity.ExternalIdentityDemand
ecologicalConnectivityQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "landscape-ecology identity"
  "ecological / landscape connectivity" Identity.wikidataQid
  (Identity.verified "Q2993449" "Wikidata ecological-connectivity concept directly inspected 2026-09-11; identity does not establish measured movement or functional connectivity")

habitatFragmentationQid : Identity.ExternalIdentityDemand
habitatFragmentationQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "landscape-ecology identity"
  "habitat fragmentation" Identity.wikidataQid
  (Identity.verified "Q913302" "Wikidata habitat-fragmentation concept directly inspected 2026-09-11; concept identity does not establish local fragmentation")

dingoQid : Identity.ExternalIdentityDemand
dingoQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "taxon identity"
  "dingo / Canis familiaris dingo" Identity.wikidataQid
  (Identity.verified "Q38584" "Wikidata dingo item directly inspected 2026-09-11; the item records disputed taxonomic treatments, and identity does not create a Melville predation or trail-use observation")

gameTrailQid : Identity.ExternalIdentityDemand
gameTrailQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "habitat-structure identity"
  "game trail / animal trail" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact Wikidata ecological-feature item located; do not substitute road/path/article/video-game items")

ecosystemEngineerQid : Identity.ExternalIdentityDemand
ecosystemEngineerQid = Identity.mkOptionalIdentityDemand
  "Tiwi megaherbivore-predator-access snowball" "ecological-role identity"
  "ecosystem engineer" Identity.wikidataQid
  (Identity.unresolved "No safely verified exact ecosystem-engineer organism-role item promoted; ecological engineering Q3738960 is a human design discipline and is a WrongType substitute")

savannaEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
savannaEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact.agda"
  "savanna disturbance / predator-access consumer"
  "577.4 — grassland ecology, including savanna ecology"
  "Q42710; Q10758650; Q58697; Q45874067; Q966490; Q2993449; Q913302; Q38584; unresolved game-trail and ecosystem-engineer QIDs"
  "DOI 10.1002/ece3.71622; Dryad DOI 10.5061/dryad.0zpc86776; DOI 10.1890/06-1599.1"

animalEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
animalEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact.agda"
  "animal ecology / predator-herbivore environment consumer"
  "591.7 — animal ecology, animals characteristic of specific environments"
  "Q42710; Q10758650; Q58697; Q45874067; Q38584"
  "DOI 10.1002/ece3.71622; DOI 10.1890/06-1599.1"

smallMammalHabitatCoordinate : Traversal.DashiKnowledgeCoordinate
smallMammalHabitatCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiMegaherbivorePredatorAccessDeweyDoiQidExact.agda"
  "Tiwi small-mammal habitat association consumer"
  "599 — Mammalia; exact taxon fibres remain separate"
  "Q303877; Q52105; Q2993449; Q913302"
  "DOI 10.1111/j.1365-2699.2006.01543.x"

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
    sourceStrength : Attribution.SourceStrength
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
  "Melville Island paired-camera study at 52 sites comparing megaherbivore game trails with adjacent undisturbed vegetation; cats and dingoes were detected substantially more often on trails. Tiwi Rangers are named collective authors and are credited with conceptualization and investigation."
  "Predator detection is not predation mortality; game-trail preference is not native-mammal demographic effect; megaherbivore control is not a proved conservation benefit; pig presence in the study-area description is not a measured trail-driver result."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

pettyEtAl2007 : MegaherbivorePredatorPrimarySource
pettyEtAl2007 = megaherbivore-predator-primary-source
  "Aaron M. Petty; Patricia A. Werner; Caroline E. R. Lehmann; Jan E. Riley; Daniel S. Banfai; Lindsay P. Elliott"
  "Savanna responses to feral buffalo in Kakadu National Park, Australia"
  "Ecological Monographs 77(3):441-463"
  2007
  "DOI 10.1890/06-1599.1"
  "Northern-Australian historical-ecology evidence that buffalo population expansion/removal altered ground-cover abundance and composition, competitive regimes and fuel loads, with interacting fire-regime consequences and hysteresis."
  "Kakadu historical cascades are a mechanism/context donor, not a Melville same-site receipt and not evidence that buffalo removal restores a prior state."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

firthEtAl2006 : MegaherbivorePredatorPrimarySource
firthEtAl2006 = megaherbivore-predator-primary-source
  "Ronald S. C. Firth; John C. Z. Woinarski; Kym G. Brennan; Craig Hempel"
  "Environmental relationships of the brush-tailed rabbit-rat, Conilurus penicillatus, and other small mammals on the Tiwi Islands, northern Australia"
  "Journal of Biogeography 33(10):1820-1837"
  2006
  "DOI 10.1111/j.1365-2699.2006.01543.x"
  "Primary Tiwi Islands habitat-association study: brush-tailed rabbit-rats were most likely in tall eucalypt forest away from watercourses; co-occurring small mammals showed distinct environmental associations and several were not recorded in plantation habitat."
  "Historical habitat association does not establish a present population state, fire-treatment effect, predator-mediated causal effect, or current plantation counterfactual without a same-object/time receipt."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

data Driver : Set where
  fireDriver
  megaherbivoreDriver
  plantationLandUseDriver : Driver

data StructuralConsumer : Set where
  groundCover
  shrubUnderstorey
  woodyStructure
  gameTrailNetwork
  habitatConnectivity
  habitatFragmentation : StructuralConsumer

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
    historicalTiwiHabitatAssociationsAcquired : Bool
    fireToShrubTiwiPaid : Bool
    megaherbivoreToTrailMelvillePaid : Bool
    trailToPredatorDetectionMelvillePaid : Bool
    megaherbivoreToGroundCoverMelvillePaid : Bool
    historicalHabitatToCurrentPopulationPaid : Bool
    predatorDetectionToMortalityPaid : Bool
    fullMultiDriverMediationPaid : Bool

open MultiDriverPredatorAccessFrontier public

canonicalMultiDriverPredatorAccessFrontier : MultiDriverPredatorAccessFrontier
canonicalMultiDriverPredatorAccessFrontier = multi-driver-predator-access-frontier
  true true true true true
  false true true false false false false

------------------------------------------------------------------------
-- BIDI interpretation: predator observations constrain what upstream landscape
-- representation must retain.  A fire-only representation cannot recover a
-- megaherbivore-created trail effect, and a megaherbivore-only representation
-- cannot recover fire history.  Historical habitat associations add a third
-- representation constraint but do not become current demographic receipts.
------------------------------------------------------------------------

data FireOnlyRepresentationRecoversAllPredatorAccess : Set where
data MegaherbivoreOnlyRepresentationRecoversAllPredatorAccess : Set where
data HistoricalHabitatAssociationMeansCurrentPopulationEffect : Set where
data PredatorDetectionMeansPredationMortality : Set where
data BuffaloRemovalRestoresHistoricalState : Set where
data PrimarySourceAdjacencyCreatesMediation : Set where
data QidCreatesLocalPresence : Set where
data QidCreatesDriverMagnitude : Set where
data DeweyCreatesCausalParent : Set where
data PigContextMeansGameTrailDriver : Set where
data EcologicalEngineeringQidMeansEcosystemEngineer : Set where

fireOnlyDoesNotRecoverAllPredatorAccess : FireOnlyRepresentationRecoversAllPredatorAccess → ⊥
fireOnlyDoesNotRecoverAllPredatorAccess ()

megaherbivoreOnlyDoesNotRecoverAllPredatorAccess : MegaherbivoreOnlyRepresentationRecoversAllPredatorAccess → ⊥
megaherbivoreOnlyDoesNotRecoverAllPredatorAccess ()

historicalHabitatAssociationDoesNotCreateCurrentPopulationEffect : HistoricalHabitatAssociationMeansCurrentPopulationEffect → ⊥
historicalHabitatAssociationDoesNotCreateCurrentPopulationEffect ()

predatorDetectionDoesNotMeanMortality : PredatorDetectionMeansPredationMortality → ⊥
predatorDetectionDoesNotMeanMortality ()

buffaloRemovalDoesNotRestoreHistoricalState : BuffaloRemovalRestoresHistoricalState → ⊥
buffaloRemovalDoesNotRestoreHistoricalState ()

primarySourceAdjacencyDoesNotCreateMediation : PrimarySourceAdjacencyCreatesMediation → ⊥
primarySourceAdjacencyDoesNotCreateMediation ()

qidDoesNotCreateLocalPresence : QidCreatesLocalPresence → ⊥
qidDoesNotCreateLocalPresence ()

qidDoesNotCreateDriverMagnitude : QidCreatesDriverMagnitude → ⊥
qidDoesNotCreateDriverMagnitude ()

deweyDoesNotCreateCausalParent : DeweyCreatesCausalParent → ⊥
deweyDoesNotCreateCausalParent ()

pigContextDoesNotCreateGameTrailDriver : PigContextMeansGameTrailDriver → ⊥
pigContextDoesNotCreateGameTrailDriver ()

ecologicalEngineeringIsWrongTypeForEcosystemEngineer : EcologicalEngineeringQidMeansEcosystemEngineer → ⊥
ecologicalEngineeringIsWrongTypeForEcosystemEngineer ()

firstUnpaidEmpiricalDiscriminator : String
firstUnpaidEmpiricalDiscriminator = Ledger.firstUnpaidEmpiricalDiscriminator

firstUnpaidMultiDriverDiscriminator : String
firstUnpaidMultiDriverDiscriminator =
  "Melville/Tiwi megaherbivore abundance or grazing pressure -> measured ground/shrub structural change on a carrier joinable to predator and native-mammal observations"

firstUnpaidHistoricalHabitatJoin : String
firstUnpaidHistoricalHabitatJoin =
  "Exact temporal/spatial weld from Firth 2006 Tiwi habitat associations to a current taxon-specific population, disturbance and predator carrier; historical habitat preference cannot pay the current state by itself"

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
