module DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapCurrentExact as Current
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact as HistoricalDump
import DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact as Genealogy
import DASHI.Wikimedia.IbrahimSnowballPostPublicationStatusPropagationBidiExact as Status
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Learning

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL PARETO FRONTIER -- LIVE REBASE
--
-- This owner is deliberately small.  It records only what survives quotienting
-- against the CURRENT roadmap and the newest concurrent Snowball owners.
--
-- Pareto rule:
--   1. drop any residual as soon as an existing owner pays it;
--   2. prefer one source-/same-object payment that unlocks many consumers;
--   3. do not create breadth merely because a Dewey/QID cell is empty;
--   4. attribution/provenance travels with every promoted edge;
--   5. QID, Dewey and DOI/canonical URL are coordinates, never truth receipts.
------------------------------------------------------------------------

data FrontierStatus : Set where
  currentHighestAlpha : FrontierStatus
  opportunisticMetadata : FrontierStatus
  consumerDrivenOnly : FrontierStatus
  paidSharedParent : FrontierStatus

record ParetoFrontierLeaf : Set where
  constructor pareto-frontier-leaf
  field
    rank : Nat
    status : FrontierStatus
    surface : String
    paidBy : String
    survivingResidual : String
    completionTest : String
    unlocks : String
    requiresNewOntology : Bool
open ParetoFrontierLeaf public

------------------------------------------------------------------------
-- Rank 1: the only known shared-parent residual in the current audit.
------------------------------------------------------------------------

historicalFirstLinkRuntime : ParetoFrontierLeaf
historicalFirstLinkRuntime = pareto-frontier-leaf
  1 currentHighestAlpha
  "Ibrahim historical First Link Network corpus / dump / parser / result same-object provenance"
  "IbrahimKnowledgeCoverageRoadmapCurrentExact; IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact; IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact"
  "2014-10-08 is the strongest concrete dump candidate, but exact artifact hash, dump-to-112-chunk lineage, parser-equivalent execution and reproduced-result same-object match remain unpaid; the paper/blog November-2014 description remains retained and unresolved against that candidate"
  "historical first-link edges beyond those directly printed by the paper may be promoted only after the exact source-object chain is paid; otherwise they remain current/revision-sensitive or candidate historical edges"
  "all historical Ibrahim traversal claims"
  false

historicalDumpBoundary : HistoricalDump.CandidateStrengtheningBoundary
historicalDumpBoundary = HistoricalDump.canonicalCandidateStrengtheningBoundary

remainingHistoricalPayment : String
remainingHistoricalPayment = HistoricalDump.remainingHistoricalPayment

------------------------------------------------------------------------
-- Rank 2: opportunistic external metadata only.
--
-- This cannot outrank the historical same-object residual because unresolved
-- QID/Dewey/DOI coordinates normally do not block unrelated domain proofs.
------------------------------------------------------------------------

metadataCleanup : ParetoFrontierLeaf
metadataCleanup = pareto-frontier-leaf
  2 opportunisticMetadata
  "QID / Dewey / DOI / canonical-link cleanup"
  "SnowballExternalIdentityAvailabilityExact; AttributedSourceCore; SymbolicVerificationDeweyQidDoiBidiExact and domain-local owners"
  "resolve exact identities/classifications only when safe; retain unresolved explicitly; never nearest-label substitute"
  "a newly resolved coordinate is attached with source role and does not change theorem status, evidentiary weight or authority"
  "navigation, source archaeology, library classification and citation linking"
  false

------------------------------------------------------------------------
-- Rank 3: new graph work is now concrete-consumer driven.
--
-- CurrentRoadmap says no known shared-parent residual remains.  A new Ibrahim
-- leaf therefore enters the frontier only when an actual consumer exposes a
-- distinction the shared grammar cannot represent.
------------------------------------------------------------------------

consumerDrivenResidual : ParetoFrontierLeaf
consumerDrivenResidual = pareto-frontier-leaf
  3 consumerDrivenOnly
  "Concrete consumer exposes a new FactorsThrough / WrongType / same-object defect"
  "IbrahimKnowledgeCoverageRoadmapCurrentExact plus the relevant domain owner"
  "not pre-enumerated: must be demonstrated by a concrete claim, source, experiment, legal element, field observation, historical object or other live consumer"
  "existing owners fail to represent one required distinction; the repair is the thinnest compositional extension that preserves attribution and provenance"
  "future geology/healthcare/petrochemistry/ethnography/media/science/law/biology/etc only when demanded"
  false

------------------------------------------------------------------------
-- Shared residuals that were live in the first Pareto cut are now PAID.
------------------------------------------------------------------------

sourceGenealogyPaid : ParetoFrontierLeaf
sourceGenealogyPaid = pareto-frontier-leaf
  0 paidSharedParent
  "Corroboration / replication / common-source dependence / evidence synthesis / consensus"
  "MemoryRepetitionSourceDependencyConsensus; EvidenceSynthesisPeerReviewConflictIndependence; ReplicationSourceGenealogyEvidenceSynthesis; SourceGenealogyIndependenceEvidenceSynthesis; InformationCascadeEvidenceDependencyHyperfabric; SystematicReviewMetaAnalysisPublicationBias"
  "only consumer-specific dependency calculations remain"
  "multiplicity, citation visibility and apparent consensus cannot manufacture provenance independence"
  "testimony, OSINT, media, science, meta-analysis, climate assessment, AI summaries"
  false

sourceGenealogyBoundary : Genealogy.SourceGenealogyIndependenceEvidenceSynthesisBoundary
sourceGenealogyBoundary = Genealogy.canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary

postPublicationStatusPaid : ParetoFrontierLeaf
postPublicationStatusPaid = pareto-frontier-leaf
  0 paidSharedParent
  "Correction / addendum / expression of concern / retraction / downstream status propagation"
  "FactCheckingVerificationMediaLiteracyCorrection; PostPublicationStatusPropagation; append-only source/evidence revision owners"
  "only exact downstream claim re-audits remain"
  "status events are append-only and object-indexed; stable DOI != current status; one retraction != every downstream conclusion false"
  "science, media, OSINT, climate, AI, legal/source monitoring"
  false

postPublicationBoundary : Status.PostPublicationStatusPropagationBoundary
postPublicationBoundary = Status.canonicalPostPublicationStatusPropagationBoundary

learningMemoryTraumaPaid : ParetoFrontierLeaf
learningMemoryTraumaPaid = pareto-frontier-leaf
  0 paidSharedParent
  "Learning / memory / trauma / testimony / replication"
  "DepthWheelMemoryHyperfabric; TraumaMemoryHypervoxelBridge; TestimonyMemoryCredibilityCorroborationExpert; LearningMemoryTraumaReplicationConsensus"
  "only concrete source-/consumer-specific claims remain"
  "same remembered surface != same latent state; extinction != erasure; trauma residual != diagnosis; repetition != independence"
  "psychology, education, testimony, trauma-memory and replication"
  false

learningBoundary : Learning.LearningMemoryTraumaReplicationConsensusBoundary
learningBoundary = Learning.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Imported policies remain authoritative.
------------------------------------------------------------------------

attributionBoundary : Attribution.AttributionSnowballBoundary
attributionBoundary = Attribution.canonicalAttributionSnowballBoundary

externalIdentityPolicy : Identity.SnowballExternalIdentityPolicy
externalIdentityPolicy = Identity.canonicalExternalIdentityPolicy

currentRoadmapCriterion : Current.RoadmapCompletionCriterion
currentRoadmapCriterion = Current.currentRoadmapCriterion

------------------------------------------------------------------------
-- Compact answer to "where does that leave us?"
------------------------------------------------------------------------

record RemainingFrontier : Set where
  constructor remaining-frontier
  field
    first : ParetoFrontierLeaf
    second : ParetoFrontierLeaf
    third : ParetoFrontierLeaf
    knownSharedParentResidualsRemain : Bool
    breadthExpansionIsCurrentPriority : Bool
open RemainingFrontier public

canonicalRemainingFrontier : RemainingFrontier
canonicalRemainingFrontier = remaining-frontier
  historicalFirstLinkRuntime
  metadataCleanup
  consumerDrivenResidual
  false
  false

record ParetoPolicy : Set where
  constructor pareto-policy
  field
    quotientCurrentRepoFirst : Bool
    paidResidualDropsFromFrontierImmediately : Bool
    sameObjectBeforeHistoricalPromotion : Bool
    provenanceBeforeMultiplicityPromotion : Bool
    attributionTravelsWithEveryPromotedEdge : Bool
    qidDeweyDoiAreNavigationNotTruth : Bool
    unresolvedMetadataBlocksUnrelatedProof : Bool
    preEnumerateEveryPossibleTopic : Bool
open ParetoPolicy public

canonicalParetoPolicy : ParetoPolicy
canonicalParetoPolicy = pareto-policy
  true true true true true true false false
