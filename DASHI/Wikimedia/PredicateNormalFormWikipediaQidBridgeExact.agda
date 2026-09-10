module DASHI.Wikimedia.PredicateNormalFormWikipediaQidBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

------------------------------------------------------------------------
-- DASHI PNF <-> PUBLIC PNF WIKIMEDIA IDENTITY BRIDGE
--
-- DASHI's PNF means Predicate Normal Form for evidence-bearing assertions.
-- The public English Wikipedia article commonly abbreviated PNF is
-- "Prenex normal form", Wikidata Q281854.  Prenex normal form is a first-order
-- logical normal form with a quantifier prefix and quantifier-free matrix.
--
-- Therefore this bridge records a related-name/logic-neighbour relation, not
-- concept identity.  The acronym collision must survive every downstream
-- projection so that Q281854 can never silently rename DASHI Predicate Normal
-- Form into prenex normal form.
--
-- Public identities inspected 2026-09-10:
--   enwiki title: Prenex normal form
--   enwiki page id: 421068
--   enwiki oldid: 1325155371
--   Wikidata item: Q281854
--   Wikidata oldid: 2306917080
-- Exact content hashes are not fabricated here; hash payment remains open.
------------------------------------------------------------------------

prenexQid : Identity.ExternalIdentityDemand
prenexQid = Identity.mkOptionalIdentityDemand
  "DASHI Predicate Normal Form external-identity bridge"
  "public PNF Wikidata identity"
  "Prenex normal form"
  Identity.wikidataQid
  (Identity.verified "Q281854" "Wikidata entity inspected 2026-09-10")

prenexWikipediaCanonical : Identity.ExternalIdentityDemand
prenexWikipediaCanonical = Identity.mkOptionalIdentityDemand
  "DASHI Predicate Normal Form external-identity bridge"
  "public PNF English Wikipedia article"
  "Prenex normal form"
  Identity.canonicalURL
  (Identity.verified
    "https://en.wikipedia.org/wiki/Prenex_normal_form"
    "enwiki page id 421068; oldid 1325155371 inspected 2026-09-10")

record WikimediaPNFIdentityCoordinate : Set where
  constructor wikimedia-pnf-identity-coordinate
  field
    wikipediaTitle : String
    wikipediaPageId : String
    wikipediaRevisionId : String
    wikidataQid : String
    wikidataRevisionId : String
    exactContentHashPaid : Bool
    inspectionDate : String
open WikimediaPNFIdentityCoordinate public

prenexCoordinate : WikimediaPNFIdentityCoordinate
prenexCoordinate = wikimedia-pnf-identity-coordinate
  "Prenex normal form"
  "421068"
  "1325155371"
  "Q281854"
  "2306917080"
  false
  "2026-09-10"

data PNFRelationship : Set where
  sameConcept : PNFRelationship
  acronymCollision : PNFRelationship
  relatedLogicalNormalForm : PNFRelationship
  implementationUsesPrenexStage : PNFRelationship
  unrelated : PNFRelationship

record PredicatePrenexBridge : Set where
  constructor predicate-prenex-bridge
  field
    dashiTerm : String
    publicTerm : String
    primaryRelationship : PNFRelationship
    secondaryRelationship : PNFRelationship
    dashiPredicateNormalFormIsPrenexNormalForm : Bool
    publicQidMayIdentifyDashiPNF : Bool
    prenexMayBeUsedAsOptionalLogicalSubstage : Bool
    optionalSubstageRequiresSeparateReceipt : Bool
open PredicatePrenexBridge public

canonicalPredicatePrenexBridge : PredicatePrenexBridge
canonicalPredicatePrenexBridge = predicate-prenex-bridge
  "Predicate Normal Form"
  "Prenex normal form"
  acronymCollision
  relatedLogicalNormalForm
  false false true true

------------------------------------------------------------------------
-- Existing DASHI Predicate Normal Form remains the semantic owner.
------------------------------------------------------------------------

predicateNormalFormBoundary : EvidencePNF.PredicateNormalFormBoundary
predicateNormalFormBoundary = EvidencePNF.canonicalPredicateNormalFormBoundary

------------------------------------------------------------------------
-- Snowball attribution role.
------------------------------------------------------------------------

publicPrenexSource : Attribution.AttributedSource
publicPrenexSource = Attribution.mkNoDOISource
  "Wikipedia contributors"
  "Prenex normal form"
  "English Wikipedia"
  "continuously revised"
  "https://en.wikipedia.org/wiki/Prenex_normal_form"
  Attribution.communitySource
  "external terminology/logic-neighbour coordinate only; not source authority for DASHI Predicate Normal Form"
  Attribution.publicAttribution

publicPrenexAttributionReceipt :
  AttributionSnowball.SourceRoleSnowballReceipt publicPrenexSource
publicPrenexAttributionReceipt =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt publicPrenexSource

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AcronymCreatesIdentity : Set where
data Q281854CreatesDashiPNFIdentity : Set where
data PrenexNormalisationCreatesEvidenceAdmissibility : Set where
data PredicateNormalFormCreatesPrenexEquivalence : Set where
data WikipediaPNFCreatesDashiAuthority : Set where

acronymDoesNotCreateIdentity : AcronymCreatesIdentity → ⊥
acronymDoesNotCreateIdentity ()

q281854DoesNotIdentifyDashiPNF : Q281854CreatesDashiPNFIdentity → ⊥
q281854DoesNotIdentifyDashiPNF ()

prenexDoesNotCreateEvidenceAdmissibility : PrenexNormalisationCreatesEvidenceAdmissibility → ⊥
prenexDoesNotCreateEvidenceAdmissibility ()

predicatePNFDoesNotCreatePrenexEquivalence : PredicateNormalFormCreatesPrenexEquivalence → ⊥
predicatePNFDoesNotCreatePrenexEquivalence ()

wikipediaDoesNotCreateDashiAuthority : WikipediaPNFCreatesDashiAuthority → ⊥
wikipediaDoesNotCreateDashiAuthority ()

record PredicateNormalFormWikimediaBoundary : Set where
  constructor predicate-normal-form-wikimedia-boundary
  field
    publicPNFIdentityRecorded : Bool
    qidRecorded : Bool
    wikipediaRevisionRecorded : Bool
    wikidataRevisionRecorded : Bool
    contentHashStillExplicitlyOpen : Bool
    acronymCollisionRetained : Bool
    sameConceptAsserted : Bool
    qidCreatesAuthority : Bool
open PredicateNormalFormWikimediaBoundary public

canonicalPredicateNormalFormWikimediaBoundary : PredicateNormalFormWikimediaBoundary
canonicalPredicateNormalFormWikimediaBoundary =
  predicate-normal-form-wikimedia-boundary
    true true true true true true false false
