module DASHI.Interop.SLRGWBReviewedWikimediaIdentityAndTieredTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia
import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB

------------------------------------------------------------------------
-- GWB REVIEWED WIKIMEDIA IDENTITY OVERLAY + TIERED TRANSPORT
--
-- Runtime:
--   fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl
--   tools/slr-discourse-reconstruct/slr_gwb_wikimedia_seed_candidates.py
--   tools/slr-discourse-reconstruct/run_gwb_wikimedia_world_follow.sh
--
-- SensibLaw transport reference:
--   src/policy/wikidata_tiered_transport.py
--
-- Normal acquisition order:
--   local/cache -> Zelph/HF Wikidata snapshot -> live Wikidata only for
--   unresolved/freshness-required work.
--
-- The online-validation lane may deliberately use live Wikidata first to test
-- the network-facing contract, but this does not change production priority.
------------------------------------------------------------------------

data IdentityScope : Set where
  exactSourceWorkIdentity : IdentityScope
  topicPersonAnchor : IdentityScope
  topicFamilyAnchor : IdentityScope
  explicitWikipediaWorkTitle : IdentityScope

record ReviewedWikimediaCoordinate : Set where
  constructor reviewedWikimediaCoordinate
  field
    documentReference : String
    qidReference : String
    wikipediaTitleReference : String
    coordinateRole : String
    identityScope : IdentityScope
    reviewReference : String
    topicAnchorEqualsSourceObject : Bool
    claimTruthPromoted : Bool
    candidateOnly : Bool

open ReviewedWikimediaCoordinate public

georgeWBushSubjectCoordinate : ReviewedWikimediaCoordinate
georgeWBushSubjectCoordinate = reviewedWikimediaCoordinate
  "GWB documents 1-6"
  "Q207"
  "George W. Bush"
  "subject-person"
  topicPersonAnchor
  "live Wikidata/Wikipedia review 2026-09-11"
  false false true

bushFamilyTopicCoordinate : ReviewedWikimediaCoordinate
bushFamilyTopicCoordinate = reviewedWikimediaCoordinate
  "GWB document 7"
  "Q2743830"
  "Bush family"
  "topic-family"
  topicFamilyAnchor
  "live Wikidata/Wikipedia review 2026-09-11"
  false false true

familyOfSecretsCoordinate : ReviewedWikimediaCoordinate
familyOfSecretsCoordinate = reviewedWikimediaCoordinate
  "GWB document 8"
  ""
  "Family of Secrets"
  "source-work"
  explicitWikipediaWorkTitle
  "live English Wikipedia review 2026-09-11; QID intentionally unresolved in overlay"
  false false true

georgeHWBushSubjectCoordinate : ReviewedWikimediaCoordinate
georgeHWBushSubjectCoordinate = reviewedWikimediaCoordinate
  "GWB document 9"
  "Q23505"
  "George H. W. Bush"
  "subject-person"
  topicPersonAnchor
  "live Wikidata/Wikipedia review 2026-09-11"
  false false true

decisionPointsCoordinate : ReviewedWikimediaCoordinate
decisionPointsCoordinate = reviewedWikimediaCoordinate
  "GWB document 10"
  "Q942966"
  "Decision Points"
  "source-work"
  exactSourceWorkIdentity
  "live Wikidata/Wikipedia review 2026-09-11"
  false false true

record WikidataTieredTransportPolicy : Set where
  constructor wikidataTieredTransportPolicy
  field
    localCacheFirst : Bool
    zelphSnapshotBeforeLive : Bool
    liveFallbackOnSnapshotMiss : Bool
    liveFallbackForFreshness : Bool
    onlineValidationMayUseLiveFirst : Bool
    qidNamespaceSharedAcrossTransports : Bool
    transportProvenanceSeparateFromEntityIdentity : Bool
    snapshotHitCreatesTruth : Bool
    liveHitCreatesTruth : Bool

open WikidataTieredTransportPolicy public

canonicalWikidataTieredTransportPolicy : WikidataTieredTransportPolicy
canonicalWikidataTieredTransportPolicy =
  wikidataTieredTransportPolicy
    true true true true true true true false false

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

wikimediaAcquisitionAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaAcquisitionAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

gwbCarrierAnchor : GWB.GWBCandidateWorldBoundary
gwbCarrierAnchor = GWB.canonicalGWBCandidateWorldBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TopicAnchorIsSourceObjectIdentity : Set where
data ZelphEntityNamespaceDiffersFromLiveWikidata : Set where
data TransportSourceCreatesSemanticAuthority : Set where
data LiveOnlineValidationReordersProductionPolicy : Set where
data ReviewedQidCreatesClaimTruth : Set where

topicAnchorDoesNotIdentifySourceObject : TopicAnchorIsSourceObjectIdentity → ⊥
topicAnchorDoesNotIdentifySourceObject ()

zelphAndLiveShareWikidataNamespace : ZelphEntityNamespaceDiffersFromLiveWikidata → ⊥
zelphAndLiveShareWikidataNamespace ()

transportDoesNotCreateAuthority : TransportSourceCreatesSemanticAuthority → ⊥
transportDoesNotCreateAuthority ()

onlineValidationDoesNotReorderProduction : LiveOnlineValidationReordersProductionPolicy → ⊥
onlineValidationDoesNotReorderProduction ()

reviewedQidDoesNotCreateTruth : ReviewedQidCreatesClaimTruth → ⊥
reviewedQidDoesNotCreateTruth ()
