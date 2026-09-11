module DASHI.Interop.SLRGWBWikimediaReplayableHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia
import DASHI.Interop.SLRGWBReviewedWikimediaIdentityAndTieredTransportExact as Tiered

------------------------------------------------------------------------
-- REPLAYABLE GWB WIKIMEDIA ACQUISITION + HANDOFF
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_wikimedia_world_follow.py
--   tools/slr-discourse-reconstruct/run_gwb_wikimedia_world_follow.sh
--   tools/slr-discourse-reconstruct/package_gwb_world_handoff.sh
--
-- Operational contract:
-- * bounded live MediaWiki requests may retry/back off on transient failure;
-- * successful responses are cached by request URL and may be replayed;
-- * cache/transport provenance is not entity identity or semantic authority;
-- * runner packages the available receipts on both success and failure;
-- * handoff archive carries metadata/receipts/models/logs/cache, but no raw
--   books or projected corpus text;
-- * archive carries a per-file SHA-256 manifest plus archive SHA-256.
------------------------------------------------------------------------

record ReplayableAcquisitionBoundary : Set where
  constructor replayableAcquisitionBoundary
  field
    retryOnTransientHttp : Bool
    exponentialBackoff : Bool
    responseCacheEnabled : Bool
    cacheHitReusesAcquisitionEvidence : Bool
    cacheHitCreatesEntityIdentity : Bool
    retrySuccessCreatesSemanticAuthority : Bool
    packageOnSuccess : Bool
    packageOnFailure : Bool
    rawBooksEmbedded : Bool
    projectedCorpusTextEmbedded : Bool
    perFileShaManifest : Bool
    archiveShaReceipt : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ReplayableAcquisitionBoundary public

canonicalReplayableAcquisitionBoundary : ReplayableAcquisitionBoundary
canonicalReplayableAcquisitionBoundary =
  replayableAcquisitionBoundary
    true true true true false false
    true true false false true true true false

wikimediaPolicyAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaPolicyAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

tieredTransportAnchor : Tiered.WikidataTieredTransportPolicy
tieredTransportAnchor = Tiered.canonicalWikidataTieredTransportPolicy

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CacheHitCreatesIdentity : Set where
data RetryCreatesTruth : Set where
data FailedRunMayDropReceipts : Set where
data HandoffMayEmbedRawBooks : Set where
data HandoffMayEmbedProjectedCorpusText : Set where

cacheHitDoesNotCreateIdentity : CacheHitCreatesIdentity → ⊥
cacheHitDoesNotCreateIdentity ()

retryDoesNotCreateTruth : RetryCreatesTruth → ⊥
retryDoesNotCreateTruth ()

failedRunStillPackagesReceipts : FailedRunMayDropReceipts → ⊥
failedRunStillPackagesReceipts ()

handoffDoesNotEmbedRawBooks : HandoffMayEmbedRawBooks → ⊥
handoffDoesNotEmbedRawBooks ()

handoffDoesNotEmbedProjectedCorpusText : HandoffMayEmbedProjectedCorpusText → ⊥
handoffDoesNotEmbedProjectedCorpusText ()

record GWBWorldHandoffReceipt : Set where
  constructor gwbWorldHandoffReceipt
  field
    schemaReference : String
    candidateWorldReference : String
    reviewedSeedReference : String
    wikimediaGraphReference : String
    httpCacheReference : String
    fileManifestReference : String
    archiveShaReference : String
    packageEvenWhenFollowFails : Bool
    rawBooksAbsent : Bool
    projectedCorpusTextAbsent : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open GWBWorldHandoffReceipt public

canonicalGWBWorldHandoffReceipt : GWBWorldHandoffReceipt
canonicalGWBWorldHandoffReceipt =
  gwbWorldHandoffReceipt
    "slr-gwb-world-handoff-v1"
    "sl.candidate_world_model.v0_1"
    "slr-gwb-wikimedia-seed-candidates-v2"
    "slr-wikimedia-world-follow-v1"
    "gwb-world/wikimedia-http-cache"
    "MANIFEST.sha256"
    "gwb-world-handoff.tar.xz.sha256"
    true true true true false
