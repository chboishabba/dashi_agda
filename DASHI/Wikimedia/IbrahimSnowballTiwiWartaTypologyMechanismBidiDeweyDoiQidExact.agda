module DASHI.Wikimedia.IbrahimSnowballTiwiWartaTypologyMechanismBidiDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiEcosystemTypologyKnowledgeAuthorityDeweyDoiQidExact as Typology
import DASHI.Wikimedia.IbrahimSnowballTiwiSame88SiteMultiDriverPredatorBidiExact as Same88

------------------------------------------------------------------------
-- TIWI WARTA TYPOLOGY -> MECHANISM BIDI
--
-- Young et al. 2025 distinguishes two local Tiwi warta savanna ecosystem
-- types.  Both can legitimately navigate through the generic savanna concept
-- and the same broad Dewey savanna-ecology class, but those coarse coordinates
-- cannot reconstruct the local ecosystem identity or its mechanism/threat
-- state.  The 88-site Melville disturbance network is a potential mechanism
-- carrier, not automatically a mapped warta-type carrier.
------------------------------------------------------------------------

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Identity.mkOptionalIdentityDemand
  "Tiwi warta typology-mechanism BIDI" "generic savanna identity"
  "savanna" Identity.wikidataQid
  (Identity.verified "Q42320" "Generic Wikidata savanna identity retained from Tiwi typology owner; it does not identify either local warta ecosystem subtype")

ecosystemQid : Identity.ExternalIdentityDemand
ecosystemQid = Identity.mkOptionalIdentityDemand
  "Tiwi warta typology-mechanism BIDI" "generic ecosystem identity"
  "ecosystem" Identity.wikidataQid
  (Identity.verified "Q37813" "Generic ecosystem identity only; local Tiwi ecosystem identity remains source-defined")

wartaLocalQid : Identity.ExternalIdentityDemand
wartaLocalQid = Identity.mkOptionalIdentityDemand
  "Tiwi warta typology-mechanism BIDI" "local Tiwi ecosystem identity"
  "warta / Tiwi local ecosystem type" Identity.wikidataQid
  (Identity.unresolved "No generic Wikidata QID promoted for the local Tiwi-language ecosystem identity; Q42320 is only the broader savanna navigation coordinate")

wartaEcologyCoordinate : Traversal.DashiKnowledgeCoordinate
wartaEcologyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiWartaTypologyMechanismBidiDeweyDoiQidExact.agda"
  "two local Tiwi warta savanna ecosystem types"
  "577.4 — grassland ecology, including savanna ecology; too coarse to recover local Tiwi ecosystem subtype"
  "Q42320; Q37813; unresolved local-warta QID"
  "DOI 10.1111/cobi.70099"

wartaMechanismCoordinate : Traversal.DashiKnowledgeCoordinate
wartaMechanismCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiWartaTypologyMechanismBidiDeweyDoiQidExact.agda"
  "Melville disturbance / predator / native-mammal mechanism consumer"
  "577.4 — savanna ecology; 591.7 animal ecology remains a separate consumer coordinate"
  "Q42320; Q146; Q45874067; Q42710; Q10758650"
  "DOI 10.1071/WR19198; DOI 10.1111/ddi.12522; DOI 10.3389/fevo.2021.739550"

wartaTypologyCrossPollinatesMechanism : Traversal.DashiFirstLinkEdge
wartaTypologyCrossPollinatesMechanism = Traversal.dashi-first-link-edge
  wartaEcologyCoordinate wartaMechanismCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "local ecosystem classification nominates a mechanism-join obligation; shared savanna classification does not create the site-level join"
  true

------------------------------------------------------------------------
-- Primary source / attribution carrier.
------------------------------------------------------------------------

record WartaPrimarySource : Set where
  constructor warta-primary-source
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

open WartaPrimarySource public

youngEtAl2025 : WartaPrimarySource
youngEtAl2025 = warta-primary-source
  "Alys R. Young; Hugh F. Davies; Margaret L. Ayre; Alana Brekelmans; Brett A. Bryan; Jane Elith; Kate Hadden; Mavis Kerinaiua; David A. Keith; Donna L. Lewis; Kinjia M. Munkara-Murray; Sarah Ryan; Michaela Spencer; Emily Nicholson"
  "Applying the IUCN Global Ecosystem Typology to classify, describe, and map ecosystems based on regional data and Indigenous knowledge"
  "Conservation Biology 39(6):e70099"
  2025
  "DOI 10.1111/cobi.70099; PMID 40641149; PMCID PMC12658940"
  "Primary Tiwi ecosystem-classification study identifying 14 ecosystem types. It distinguishes two eucalypt savanna ecosystem types, both called warta in Tiwi, using species composition and soil moisture/composition rather than treating generic savanna identity or canopy cover as sufficient. Fire and moisture are reported as major ecosystem processes across many Tiwi ecosystem types."
  "The classification/map does not by itself attach an 88-site mammal/predator observation to an exact warta subtype, prove a local threat effect, create Country authority, or make generic QID/Dewey coordinates equivalent to the local ecosystem identity."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Local identity is finer than generic QID or Dewey classification.
------------------------------------------------------------------------

data WartaSubtype : Set where
  eucalyptOpenForestSavanna
  eucalyptMixedSpeciesSavanna : WartaSubtype

genericSavannaQidOf : WartaSubtype → String
genericSavannaQidOf _ = "Q42320"

deweySavannaClassOf : WartaSubtype → String
deweySavannaClassOf _ = "577.4"

localIdentityOf : WartaSubtype → String
localIdentityOf eucalyptOpenForestSavanna = "Young et al. 2025 type 1: warta eucalypt open forest savanna"
localIdentityOf eucalyptMixedSpeciesSavanna = "Young et al. 2025 type 2: warta eucalypt and mixed species savanna"

record WartaCompressionCounterexample : Set where
  constructor warta-compression-counterexample
  field
    left : WartaSubtype
    right : WartaSubtype
    sameGenericSavannaQid : genericSavannaQidOf left ≡ genericSavannaQidOf right
    sameDeweySavannaClass : deweySavannaClassOf left ≡ deweySavannaClassOf right
    localTypesRemainDistinct : Bool
    distinctionReference : String

open WartaCompressionCounterexample public

canonicalWartaCompressionCounterexample : WartaCompressionCounterexample
canonicalWartaCompressionCounterexample = warta-compression-counterexample
  eucalyptOpenForestSavanna eucalyptMixedSpeciesSavanna refl refl true
  "Young et al. 2025 Table 1/results distinguish type 1 and type 2 by species composition and soil moisture/composition while both remain savanna/warta at the coarse navigation level"

------------------------------------------------------------------------
-- Typology -> mechanism join frontier.
------------------------------------------------------------------------

record WartaMechanismJoinFrontier : Set where
  constructor warta-mechanism-join-frontier
  field
    YoungPrimarySourceAcquired : Bool
    localWartaTypesAcquired : Bool
    savannaQidAcquired : Bool
    dewey5774Acquired : Bool
    same88MechanismNetworkAcquired : Bool
    genericSavannaIdentityPaid : Bool
    localWartaIdentityPaid : Bool
    exact88SiteToWartaSubtypePaid : Bool
    sameTimeTypologyMechanismPaid : Bool
    subtypeSpecificFireEffectPaid : Bool
    subtypeSpecificHerbivoreEffectPaid : Bool
    subtypeSpecificPredatorEffectPaid : Bool
    subtypeSpecificNativeFaunaEffectPaid : Bool
    fullTypologyMechanismMediationPaid : Bool

open WartaMechanismJoinFrontier public

canonicalWartaMechanismJoinFrontier : WartaMechanismJoinFrontier
canonicalWartaMechanismJoinFrontier = warta-mechanism-join-frontier
  true true true true true
  true true
  false false false false false false false

------------------------------------------------------------------------
-- BIDI / WrongType barriers.
------------------------------------------------------------------------

data GenericSavannaQidRecoversWartaSubtype : Set where
data Dewey5774RecoversWartaSubtype : Set where
data SameSavannaClassMeansSameMechanism : Set where
data EcosystemMapCreatesSiteJoin : Set where
data SameIslandCreatesWartaSubtype : Set where
data TypologyThreatModelCreatesMeasuredEffect : Set where
data ScientificClassificationCreatesCountryAuthority : Set where
data PrimarySourceAdjacencyCreatesSameObject : Set where

genericSavannaQidDoesNotRecoverWartaSubtype : GenericSavannaQidRecoversWartaSubtype → ⊥
genericSavannaQidDoesNotRecoverWartaSubtype ()

dewey5774DoesNotRecoverWartaSubtype : Dewey5774RecoversWartaSubtype → ⊥
dewey5774DoesNotRecoverWartaSubtype ()

sameSavannaClassDoesNotMeanSameMechanism : SameSavannaClassMeansSameMechanism → ⊥
sameSavannaClassDoesNotMeanSameMechanism ()

ecosystemMapDoesNotCreateSiteJoin : EcosystemMapCreatesSiteJoin → ⊥
ecosystemMapDoesNotCreateSiteJoin ()

sameIslandDoesNotCreateWartaSubtype : SameIslandCreatesWartaSubtype → ⊥
sameIslandDoesNotCreateWartaSubtype ()

typologyThreatModelDoesNotCreateMeasuredEffect : TypologyThreatModelCreatesMeasuredEffect → ⊥
typologyThreatModelDoesNotCreateMeasuredEffect ()

scientificClassificationDoesNotCreateCountryAuthority : ScientificClassificationCreatesCountryAuthority → ⊥
scientificClassificationDoesNotCreateCountryAuthority ()

primarySourceAdjacencyDoesNotCreateSameObject : PrimarySourceAdjacencyCreatesSameObject → ⊥
primarySourceAdjacencyDoesNotCreateSameObject ()

------------------------------------------------------------------------
-- Snowball acquisition/payment remains separate.
------------------------------------------------------------------------

record WartaMechanismAcquisitionState : Set where
  constructor warta-mechanism-acquisition-state
  field
    Young2025Acquired : Bool
    localNamesAcquired : Bool
    qidCoordinatesAcquired : Bool
    deweyCoordinatesAcquired : Bool
    same88SourcesAcquired : Bool
    mapMethodAcquired : Bool
    threatModelsAcquired : Bool
    outOfOrderEvidenceRetained : Bool

record WartaMechanismPaymentState : Set where
  constructor warta-mechanism-payment-state
  field
    sourceIdentityPaid : Bool
    sourceAttributionPaid : Bool
    localTypeIdentityPaid : Bool
    genericQidIdentityPaid : Bool
    deweyClassificationPaid : Bool
    exactSpatialJoinPaid : Bool
    exactTemporalJoinPaid : Bool
    mechanismConsumerPaid : Bool
    causalEffectPaid : Bool
    managementOutcomePaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceWartaMechanismPayment :
  WartaMechanismAcquisitionState → WartaMechanismPaymentState → WartaMechanismPaymentState
snowballAcquisitionDoesNotAdvanceWartaMechanismPayment _ payment = payment

firstUnpaidSpatialJoin : String
firstUnpaidSpatialJoin =
  "Exact spatial crosswalk from each Melville 88-site disturbance/predator/native-mammal observation site to Young et al. 2025 local ecosystem type (especially warta type 1 versus type 2)"

firstUnpaidMechanismJoin : String
firstUnpaidMechanismJoin =
  "After spatial identity is paid, consumer-specific test of whether fire/herbivore/predator/native-fauna effects differ by local warta subtype; generic savanna QID or Dewey class cannot pay this"

priorTypologyFirstUnpaid : String
priorTypologyFirstUnpaid = Typology.firstUnpaidTypologyToMechanismDiscriminator

priorSame88FirstUnpaid : String
priorSame88FirstUnpaid = Same88.firstUnpaidMultiDriverDiscriminator

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
