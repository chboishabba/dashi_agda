module DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Wikimedia.NativePropertyTripleProjectionExact as Property
import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB

------------------------------------------------------------------------
-- WIKIMEDIA-FIRST WORLD ACQUISITION
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_gwb_wikimedia_seed_candidates.py
--   tools/slr-discourse-reconstruct/slr_wikimedia_world_follow.py
--   tools/slr-discourse-reconstruct/run_gwb_wikimedia_world_follow.sh
--
-- The acquisition order is deliberately narrower than generic web search:
--
--   existing candidate world
--     -> explicit Wikidata/Wikipedia coordinates
--     -> bounded Wikidata item-valued property graph
--     -> parent / part / surrounding context
--     -> Wikipedia links / categories
--     -> current first-mainspace-link candidate follow
--     -> broader Ibrahim/Snowball acquisition only if consumer debt remains.
--
-- Current first-link traversal is NOT claimed to reproduce Ibrahim et al.'s
-- historical English Wikipedia snapshot/parser.  It is a bounded present-day
-- acquisition heuristic carried under the same non-authority discipline.
------------------------------------------------------------------------

data WorldAcquisitionStage : Set where
  existingCandidateWorld : WorldAcquisitionStage
  explicitWikidataIdentity : WorldAcquisitionStage
  wikidataItemPropertyGraph : WorldAcquisitionStage
  parentPartSurroundingGraph : WorldAcquisitionStage
  wikipediaRelatedCategorySurface : WorldAcquisitionStage
  currentFirstLinkCandidate : WorldAcquisitionStage
  broaderSnowball : WorldAcquisitionStage

record WikimediaFirstAcquisitionPolicy : Set where
  constructor wikimediaFirstAcquisitionPolicy
  field
    qidIdentityBeforeBroadWeb : Bool
    itemPropertiesBeforeBroadWeb : Bool
    parentPartSurroundingBeforeBroadWeb : Bool
    wikipediaRelatedBeforeBroadWeb : Bool
    currentFirstLinkBeforeBroadWeb : Bool
    broaderSnowballOnlyAfterWikimediaResidual : Bool
    metadataSearchCandidateCreatesIdentity : Bool
    qidCreatesTruth : Bool
    propertyTripleCreatesNativeAuthority : Bool
    currentFirstLinkEqualsHistoricalIbrahimParser : Bool

open WikimediaFirstAcquisitionPolicy public

canonicalWikimediaFirstAcquisitionPolicy : WikimediaFirstAcquisitionPolicy
canonicalWikimediaFirstAcquisitionPolicy =
  wikimediaFirstAcquisitionPolicy
    true true true true true true
    false false false false

record WikimediaSeedCandidate : Set where
  constructor wikimediaSeedCandidate
  field
    seedReference : String
    sourceDocumentReference : String
    qidReference : String
    wikipediaTitleReference : String
    metadataSearchLabelReference : String
    identityPaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WikimediaSeedCandidate public

record WikimediaGraphFollowReceipt : Set where
  constructor wikimediaGraphFollowReceipt
  field
    sourceWorldReference : String
    seedReference : String
    qidNodeReference : String
    itemPropertyEdgeReference : String
    parentEdgeReference : String
    surroundingEdgeReference : String
    wikipediaRelatedReference : String
    currentFirstLinkCandidateReference : String
    ibrahimParserEquivalencePaid : Bool
    historicalSnapshotIdentityPaid : Bool
    broadSnowballStartedBeforeWikimediaResidual : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WikimediaGraphFollowReceipt public

canonicalGWBWikimediaFollowBoundary : WikimediaGraphFollowReceipt
canonicalGWBWikimediaFollowBoundary =
  wikimediaGraphFollowReceipt
    "sl.candidate_world_model.v0_1 / SLRGWBCandidateWorldProjectionExact"
    "slr-gwb-wikimedia-seed-candidates-v1"
    "Wikidata wbgetentities candidate node"
    "NativePropertyTripleProjectionExact-compatible item-valued edge"
    "P31/P279/P361/P131 parent-context candidate"
    "bounded item-valued surrounding/related property candidate"
    "Wikipedia links/categories acquisition surface"
    "current-first-mainspace-link-candidate"
    false false false true false

------------------------------------------------------------------------
-- Cross-pollination anchors.
------------------------------------------------------------------------

ibrahimTraversalPolicyAnchor : Ibrahim.DashiFirstLinkPolicy
ibrahimTraversalPolicyAnchor = Ibrahim.canonicalDashiFirstLinkPolicy

nativePropertyBoundaryAnchor : Property.NativePropertyTripleBoundary
nativePropertyBoundaryAnchor = Property.canonicalNativePropertyTripleBoundary

gwbCarrierAnchor : GWB.GWBCandidateWorldBoundary
gwbCarrierAnchor = GWB.canonicalGWBCandidateWorldBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetadataSearchCandidateIsIdentity : Set where
data QidIdentityIsClaimTruth : Set where
data WikimediaPropertyEdgeIsNativeStatementAuthority : Set where
data WikipediaCategoryIsSemanticImplication : Set where
data CurrentFirstLinkIsExactHistoricalIbrahimEdge : Set where
data WikimediaResidualMayBeSkippedBeforeBroadSnowball : Set where

metadataSearchDoesNotPayIdentity : MetadataSearchCandidateIsIdentity → ⊥
metadataSearchDoesNotPayIdentity ()

qidDoesNotPayTruth : QidIdentityIsClaimTruth → ⊥
qidDoesNotPayTruth ()

propertyEdgeDoesNotBecomeNativeAuthority : WikimediaPropertyEdgeIsNativeStatementAuthority → ⊥
propertyEdgeDoesNotBecomeNativeAuthority ()

categoryDoesNotCreateSemanticImplication : WikipediaCategoryIsSemanticImplication → ⊥
categoryDoesNotCreateSemanticImplication ()

currentFirstLinkDoesNotBecomeHistoricalIbrahimEdge :
  CurrentFirstLinkIsExactHistoricalIbrahimEdge → ⊥
currentFirstLinkDoesNotBecomeHistoricalIbrahimEdge ()

broadSnowballRequiresWikimediaResidual :
  WikimediaResidualMayBeSkippedBeforeBroadSnowball → ⊥
broadSnowballRequiresWikimediaResidual ()
