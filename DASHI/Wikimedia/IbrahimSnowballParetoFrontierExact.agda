module DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapCurrentExact as Current
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact as HistoricalDump
import DASHI.Wikimedia.IbrahimFirstLinkNovember06ProducerPathStrengtheningExact as November06
import DASHI.Wikimedia.IbrahimFirstLinkProducerOutputPathResidualExact as OutputPath
import DASHI.Wikimedia.IbrahimFirstLinkRepositoryHistoryCustodyPruningExact as HistoryPruning
import DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact as Genealogy
import DASHI.Wikimedia.IbrahimSnowballPostPublicationStatusPropagationBidiExact as Status
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Learning

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL PARETO FRONTIER -- LIVE REBASE
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
-- Rank 1: only known shared-parent residual.
------------------------------------------------------------------------

historicalFirstLinkRuntime : ParetoFrontierLeaf
historicalFirstLinkRuntime = pareto-frontier-leaf
  1 currentHighestAlpha
  "Ibrahim historical First Link Network corpus / dump / parser / result same-object provenance"
  "IbrahimKnowledgeCoverageRoadmapCurrentExact; IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact; IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact; IbrahimFirstLinkNovember06ProducerPathStrengtheningExact; IbrahimFirstLinkProducerOutputPathResidualExact; IbrahimFirstLinkRepositoryHistoryCustodyPruningExact"
  "2014-11-06 remains the strongest producer-path DATE candidate: methods say November 2014 and 112 UVM cores; producer preprocessing names enwiki_20141106.xml; chunk-preparation code enumerates 112 small*.xml names; run_fln.py submits 112 indexed jobs; combine_fln.py merges 112 numbered JSONs into fln.json; author appendix identifies a published 505 MB data/fln.json. create_fln.py writes numbered shards to true_flnetwork while combine_fln.py reads flnetwork. Public Git path archaeology now prunes an older committed path-fix route: create_fln.py and the incomplete results/README.md both first appear in the 2015-10-04 ready snapshot, with no earlier committed revision recovered; current code still contains the mismatch and no committed move/copy/rename receipt. Therefore the remaining same-object payment must come from external execution/custody evidence, published-data acquisition, or another non-committed artifact. Exact dump variant/hash, raw pre-split command/chunk hashes, executed source object, shard custody, parser-equivalent reproduction and published-result hash comparison remain unpaid. The 20141008 parser comment remains a conflicting/stale cue."
  "historical first-link edges beyond those directly printed by the paper may be promoted only after the exact source-object chain is paid; otherwise they remain current/revision-sensitive or candidate historical edges"
  "all historical Ibrahim traversal claims"
  false

historicalDumpBoundary : HistoricalDump.CandidateStrengtheningBoundary
historicalDumpBoundary = HistoricalDump.canonicalCandidateStrengtheningBoundary

november06Boundary : November06.November06StrengtheningBoundary
november06Boundary = November06.canonicalNovember06StrengtheningBoundary

outputPathBoundary : OutputPath.ProducerOutputPathBoundary
outputPathBoundary = OutputPath.canonicalProducerOutputPathBoundary

historyPruningBoundary : HistoryPruning.RepositoryHistoryCustodyBoundary
historyPruningBoundary = HistoryPruning.canonicalRepositoryHistoryCustodyBoundary

remainingHistoricalPayment : String
remainingHistoricalPayment =
  "Public committed-history search for an older path-consistent create_fln.py is now pruned. Recover exact 2014-11-06 input artifact identity/hash and raw dump-to-112 split receipt; recover an external execution/custody artifact connecting true_flnetwork outputs to flnetwork inputs or another historically executed path-consistent source object; acquire/hash the author-hosted data/fln.json; rerun parser/constructor equivalently; compare hashes/semantic object identity."

------------------------------------------------------------------------
-- Rank 2: opportunistic metadata only.
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
-- Rank 3: concrete-consumer-driven only.
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
-- Shared residuals already paid.
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
  historicalFirstLinkRuntime metadataCleanup consumerDrivenResidual false false

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
canonicalParetoPolicy = pareto-policy true true true true true true false false
