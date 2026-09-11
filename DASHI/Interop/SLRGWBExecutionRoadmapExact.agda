module DASHI.Interop.SLRGWBExecutionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB

------------------------------------------------------------------------
-- GWB EXECUTION ROADMAP
--
-- This roadmap is updated from the validated 2026-09-11 handoff.  The SLR
-- runtime / CandidateWorldModel / replayable Wikimedia plumbing is now paid.
-- The live frontier is claim-relative source role + consumer-specific world
-- residual contraction, not more parser or transport architecture.
------------------------------------------------------------------------

data GWBStageState : Set where
  paid : GWBStageState
  implementedAwaitingRuntime : GWBStageState
  active : GWBStageState
  next : GWBStageState
  notApplicableWithoutNewEvidence : GWBStageState

record GWBRoadmapCoordinate : Set where
  constructor gwbRoadmapCoordinate
  field
    stageReference : String
    state : GWBStageState
    paymentReference : String
    remainingResidualReference : String

open GWBRoadmapCoordinate public

gwbSLRRoadmap : List GWBRoadmapCoordinate
gwbSLRRoadmap =
  gwbRoadmapCoordinate
    "ten-document source projection + SLR direct/reference execution parity"
    paid
    "sensiblaw.gwb-full-certification-receipt.v0_1: 10 docs / 41,134 sentences / parity_failed=0 / published=false"
    "domain semantics are not paid by runtime parity"
  ∷ gwbRoadmapCoordinate
    "GWB certification -> SensibLaw CandidateWorldModel projection"
    paid
    "slr-gwb-candidate-world-v1: 41,134 claims / 41,124 structural relations / provenance=10"
    "candidate sentence carrier is not canonical claim semantics"
  ∷ gwbRoadmapCoordinate
    "SensibLaw normalization parity at GWB scale"
    paid
    "normalization_drift=false; zero-valued status classes omitted"
    "normalization parity does not create source/world truth"
  ∷ gwbRoadmapCoordinate
    "reviewed Wikimedia seed overlay"
    paid
    "10 reviewed seeds / 9 explicit QIDs / 1 explicit Wikipedia title / unseeded=0"
    "topic anchor remains distinct from source-object identity"
  ∷ gwbRoadmapCoordinate
    "replayable bounded Wikimedia world follow"
    paid
    "51 QID nodes / 850 property edges / 162 parent / 688 surrounding-related / 41 Wikipedia pages / post-follow normalization_drift=false"
    "current first-link candidates are not exact historical Ibrahim parser edges"
  ∷ gwbRoadmapCoordinate
    "cache-only deterministic replay + one-tar handoff"
    paid
    "134 cache hits / 0 network requests on replay; replayable handoff SHA receipt; no raw books/projected corpus text"
    "cache/transport provenance does not create identity or semantic authority"
  ∷ gwbRoadmapCoordinate
    "Wikimedia source-work identity residual contraction"
    paid
    "source_work_identity_paid=2; unpaid=8; topic_anchor_paid=8; runtime_resolved_work_identities=1; post-contraction normalization_drift=false"
    "eight documents retain exact source-work identity debt; claim truth remains unpaid"
  ∷ gwbRoadmapCoordinate
    "claim-relative source-role atlas"
    implementedAwaitingRuntime
    "fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl / SLRGWBClaimRelativeSourceRoleAtlasExact"
    "validate role attachment without collapsing official, institutional, secondary, investigative and first-person source classes"
  ∷ gwbRoadmapCoordinate
    "consumer-specific graph residual contraction"
    active
    "reuse Q/P parent/surrounding graph only against declared consumer obligations"
    "identify which world residual dimensions are paid by graph evidence and which survive to Snowball"
  ∷ gwbRoadmapCoordinate
    "canonical GWB claim/evidence projection"
    next
    "requires explicit claim fixtures or source-paid extraction receipts after source-role typing"
    "sentence identity and adjacency alone cannot manufacture canonical claims"
  ∷ gwbRoadmapCoordinate
    "broader Snowball acquisition"
    next
    "admissible only for consumer residuals surviving reviewed Wikimedia graph completion"
    "do not broaden research merely because eight source-work identities remain unpaid unless a consumer requires them"
  ∷ gwbRoadmapCoordinate
    "broadcast speaker/path gold"
    notApplicableWithoutNewEvidence
    "GWB source set is biography/book prose, not a speaker-labelled broadcast transcript"
    "do not reuse ABC speaker-cut heuristics as if they were prose semantics"
  ∷ []

record GWBExecutionBoundary : Set where
  constructor gwbExecutionBoundary
  field
    transcriptSpecificDiscourseStackReusedBlindly : Bool
    certifiedSentenceCarrierReused : Bool
    sourceProjectionHashesReused : Bool
    rawBooksEmbeddedInWorldArtifact : Bool
    normalizationParityRequiredBeforeSemanticExpansion : Bool
    sourceRoleMayBeCollapsedAcrossAllDocuments : Bool
    canonicalClaimIdentityMayBeInferredFromAdjacency : Bool
    wikimediaGraphMayPromoteClaimTruth : Bool
    topicAnchorMayBecomeSourceObjectIdentity : Bool
    broadSnowballMayStartBeforeConsumerResidual : Bool

open GWBExecutionBoundary public

canonicalGWBExecutionBoundary : GWBExecutionBoundary
canonicalGWBExecutionBoundary = gwbExecutionBoundary
  false true true false true false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GWBProseIsBroadcastTranscript : Set where
data CertifiedAdjacencyIsCanonicalClaimGraph : Set where
data FirstPersonMemoirIsPrimaryForAllEvents : Set where
data OfficialBiographyIsIndependentHistoricalProof : Set where
data SecondaryBookMayBePromotedBySLRParity : Set where
data WikimediaGraphCreatesClaimTruth : Set where
data TopicAnchorIsSourceObjectIdentity : Set where
data SnowballMayIgnoreConsumerResidual : Set where

proseIsNotBroadcastTranscript : GWBProseIsBroadcastTranscript → ⊥
proseIsNotBroadcastTranscript ()

adjacencyIsNotCanonicalClaimGraph : CertifiedAdjacencyIsCanonicalClaimGraph → ⊥
adjacencyIsNotCanonicalClaimGraph ()

memoirIsNotPrimaryForAllEvents : FirstPersonMemoirIsPrimaryForAllEvents → ⊥
memoirIsNotPrimaryForAllEvents ()

officialBiographyIsNotIndependentProof : OfficialBiographyIsIndependentHistoricalProof → ⊥
officialBiographyIsNotIndependentProof ()

parityDoesNotPromoteSecondaryBook : SecondaryBookMayBePromotedBySLRParity → ⊥
parityDoesNotPromoteSecondaryBook ()

wikimediaGraphDoesNotCreateTruth : WikimediaGraphCreatesClaimTruth → ⊥
wikimediaGraphDoesNotCreateTruth ()

topicAnchorDoesNotIdentifySourceObject : TopicAnchorIsSourceObjectIdentity → ⊥
topicAnchorDoesNotIdentifySourceObject ()

snowballRequiresConsumerResidual : SnowballMayIgnoreConsumerResidual → ⊥
snowballRequiresConsumerResidual ()

gwbProjectionAnchor : GWB.GWBCandidateWorldBoundary
gwbProjectionAnchor = GWB.canonicalGWBCandidateWorldBoundary
