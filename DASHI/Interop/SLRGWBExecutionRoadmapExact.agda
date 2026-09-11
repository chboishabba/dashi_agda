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
-- Updated from validated 2026-09-11 runtime handoffs.  The SLR runtime,
-- CandidateWorldModel ABI, replayable Wikimedia graph, identity contraction,
-- claim-relative source roles, multilingual parser compatibility, and the
-- first PNF role-family experiment are paid.  The active frontier is semantic
-- closure/gap propagation and joined world-research iteration.
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
  gwbRoadmapCoordinate "ten-document source projection + SLR direct/reference execution parity" paid
    "sensiblaw.gwb-full-certification-receipt.v0_1: 10 docs / 41,134 sentences / parity_failed=0 / published=false"
    "domain semantics are not paid by runtime parity"
  ∷ gwbRoadmapCoordinate "GWB certification -> SensibLaw CandidateWorldModel projection" paid
    "slr-gwb-candidate-world-v1: 41,134 claims / 41,124 structural relations / provenance=10"
    "candidate sentence carrier is not canonical claim semantics"
  ∷ gwbRoadmapCoordinate "SensibLaw normalization parity at GWB scale" paid
    "normalization_drift=false; zero-valued status classes omitted"
    "normalization parity does not create source/world truth"
  ∷ gwbRoadmapCoordinate "reviewed Wikimedia seed overlay" paid
    "10 reviewed seeds / 9 explicit QIDs / 1 explicit Wikipedia title / unseeded=0"
    "topic anchor remains distinct from source-object identity"
  ∷ gwbRoadmapCoordinate "replayable bounded Wikimedia world follow" paid
    "51 QID nodes / 850 property edges / 162 parent / 688 surrounding-related / 41 Wikipedia pages / post-follow normalization_drift=false"
    "current first-link candidates are not exact historical Ibrahim parser edges"
  ∷ gwbRoadmapCoordinate "cache-only deterministic replay + streamed one-tar handoff v2" paid
    "v2 archive SHA-256 956c92ea0e5f402b8711f76d4146a2cc870248880bf693a0549b7a42f2d75594; no full staging copy; no raw/projected corpus text"
    "transport/package reproducibility does not create semantic authority"
  ∷ gwbRoadmapCoordinate "Wikimedia source-work identity residual contraction" paid
    "source_work_identity_paid=2; unpaid=8; topic_anchor_paid=8; runtime_resolved_work_identities=1; normalization_drift=false"
    "eight documents retain exact source-work identity debt; claim truth remains unpaid"
  ∷ gwbRoadmapCoordinate "claim-relative source-role atlas + CandidateWorldModel attachment" paid
    "roles=10 / primary claim classes=11 / negative authority constraints=19 / normalization_drift=false"
    "source role constrains consumers but does not create event truth"
  ∷ gwbRoadmapCoordinate "multilingual shared-QID Wikimedia/parser compatibility" paid
    "qids=4 / language_surfaces=13 / trained_parser_surfaces=13 / fallback=0 across en/es/fr/de"
    "shared QID pays identity only; translation/semantic equivalence remain residual"
  ∷ gwbRoadmapCoordinate "multilingual PNF role-family compatibility" paid
    "qids=4 / surfaces=13 / language_pairs=18 / surfaces_with_subject_predicate_object=10 / core-compatible pairs=9"
    "role overlap remains structural evidence only; sentence alignment and claim-semantic equivalence=false"
  ∷ gwbRoadmapCoordinate "Simple English Wikipedia peer surface" implementedAwaitingRuntime
    "multilingual compatibility now requests simplewiki and parses it with the trained English dependency model while retaining language=simple provenance"
    "measure actual sitelink/surface availability; do not presume simplewiki is a subset or translation of enwiki"
  ∷ gwbRoadmapCoordinate "multilingual semantic closure + per-surface gap propagation" implementedAwaitingRuntime
    "slr-semantic-world-closure-v1 / SLRSemanticWorldClosureExact"
    "validate canonical QID/QP/link atoms, attributed propagation, target_surface_asserted=false, and next acquisition obligations"
  ∷ gwbRoadmapCoordinate "joined GWB/AU/Brexit WorldResearchIteration" implementedAwaitingRuntime
    "slr-world-research-tranche-join-v1 + slr-world-research-iteration-v1 / SLRWorldResearchTrancheConvergenceExact"
    "GWB world-ready; AU retained-source-ready; Brexit source-unpaid until retained narrative/source acquisition"
  ∷ gwbRoadmapCoordinate "consumer-specific graph residual contraction" active
    "reuse semantic closure, Q/P parent/surrounding graph and claim-relative source roles against declared consumer obligations"
    "identify which semantic/world residuals are paid and which survive to acquisition"
  ∷ gwbRoadmapCoordinate "advisory external ontology fallback" next
    "Wikidata primary; DBpedia/YAGO/WordNet/Schema.org/Umbel demand-driven via SLRExternalOntologyEnrichmentRouterExact"
    "invoke only for declared residuals that Wikimedia/source-role evidence cannot pay"
  ∷ gwbRoadmapCoordinate "canonical GWB claim/evidence projection" next
    "requires source-paid claim extraction beyond entity/link closure"
    "semantic context and adjacency alone cannot manufacture canonical claims"
  ∷ gwbRoadmapCoordinate "broader Snowball acquisition" next
    "admissible only for residuals surviving reviewed Wikimedia/external-ontology completion"
    "do not broaden merely because source-work identities remain unpaid"
  ∷ gwbRoadmapCoordinate "broadcast speaker/path gold" notApplicableWithoutNewEvidence
    "GWB source set is biography/book prose, not a speaker-labelled broadcast transcript"
    "do not reuse ABC speaker-cut heuristics as prose semantics"
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
    sharedQidMayPromoteTranslationEquivalence : Bool
    parserCompatibilityMayPromoteSemanticEquivalence : Bool
    pnfRoleOverlapMayPromoteClaimSemanticEquivalence : Bool
    semanticPropagationMayRewriteTargetSurface : Bool
    simpleWikiMayBePresumedEnglishSubset : Bool
    sourceUnpaidTrancheMayContributeSemanticAtoms : Bool
    broadSnowballMayStartBeforeConsumerResidual : Bool

open GWBExecutionBoundary public

canonicalGWBExecutionBoundary : GWBExecutionBoundary
canonicalGWBExecutionBoundary = gwbExecutionBoundary
  false true true false true false false false false false false false false false false false

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
data SharedQidIsTranslationEquivalence : Set where
data ParserCompatibilityIsSemanticEquivalence : Set where
data PNFRoleOverlapIsClaimSemanticEquivalence : Set where
data SemanticPropagationRewritesTargetSurface : Set where
data SimpleWikiIsEnglishSubset : Set where
data SourceUnpaidTrancheContributesAtoms : Set where
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
sharedQidDoesNotCreateTranslationEquivalence : SharedQidIsTranslationEquivalence → ⊥
sharedQidDoesNotCreateTranslationEquivalence ()
parserCompatibilityDoesNotCreateSemanticEquivalence : ParserCompatibilityIsSemanticEquivalence → ⊥
parserCompatibilityDoesNotCreateSemanticEquivalence ()
pnfRoleOverlapDoesNotCreateSemanticEquivalence : PNFRoleOverlapIsClaimSemanticEquivalence → ⊥
pnfRoleOverlapDoesNotCreateSemanticEquivalence ()
semanticPropagationDoesNotRewriteTargetSurface : SemanticPropagationRewritesTargetSurface → ⊥
semanticPropagationDoesNotRewriteTargetSurface ()
simpleWikiIsNotPresumedEnglishSubset : SimpleWikiIsEnglishSubset → ⊥
simpleWikiIsNotPresumedEnglishSubset ()
sourceUnpaidTrancheCannotContributeAtoms : SourceUnpaidTrancheContributesAtoms → ⊥
sourceUnpaidTrancheCannotContributeAtoms ()
snowballRequiresConsumerResidual : SnowballMayIgnoreConsumerResidual → ⊥
snowballRequiresConsumerResidual ()

gwbProjectionAnchor : GWB.GWBCandidateWorldBoundary
gwbProjectionAnchor = GWB.canonicalGWBCandidateWorldBoundary
