module DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.WorldModel.PredicateNormalWorldModelCore as PNW
import DASHI.Law.SensibLawSparseWorldModelAcquisitionExact as Sparse
import DASHI.Cognition.PNF.SensibLawDiscourseQualityAuditExact as Quality
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Ibrahim
import DASHI.Interop.ITIRSensiBlawStreamlineArchitecture as ITIRSL

------------------------------------------------------------------------
-- SLR / WORLD-MODEL SUITE CONVERGENCE ROADMAP
--
-- Cross-repo division of labour:
--   SensibLaw  : generic CandidateWorldModel / review / promotion surface
--   ITIR-suite : generic source -> span/PNF -> world-model compiler
--   TiRCorder  : contested event/narrative interpretation and provenance
--   StatiBaker : append-only temporal state / replay / drift surface
--   DASHI      : typed proposal, promotion, sparse-world and proof boundaries
--   SLR        : discourse/document reconstruction + candidate producers
--
-- Validated 2026-09-11 state:
-- * parser/reconstruction/carrier plumbing is mature and largely frozen;
-- * ABC proves claim-local fragment -> residual inheritance -> evidence
--   contraction without claim-truth promotion;
-- * GWB proves 41k-sentence CandidateWorldModel scale, replayable Wikimedia
--   graph enrichment, cache-only replay and source-identity contraction;
-- * live frontier is consumer-specific world residual contraction and
--   canonical claim/evidence projection, not more boundary heuristics.
------------------------------------------------------------------------

data SuiteOwner : Set where
  sensibLawOwner : SuiteOwner
  itirSuiteOwner : SuiteOwner
  tircorderOwner : SuiteOwner
  statiBakerOwner : SuiteOwner
  dashiOwner : SuiteOwner
  slrRuntimeOwner : SuiteOwner


data SuiteResponsibility : Set where
  candidateWorldCarrier : SuiteResponsibility
  genericSourceCompiler : SuiteResponsibility
  contestedNarrativeCarrier : SuiteResponsibility
  appendOnlyTimeAxis : SuiteResponsibility
  typedProofBoundary : SuiteResponsibility
  discourseReconstruction : SuiteResponsibility
  evidenceSnowball : SuiteResponsibility
  reviewPromotionBoundary : SuiteResponsibility

record SuiteOwnershipReceipt : Set where
  constructor suiteOwnershipReceipt
  field
    owner : SuiteOwner
    responsibility : SuiteResponsibility
    sourceReference : String
    parallelArchitectureCreated : Bool

open SuiteOwnershipReceipt public

sensibLawWorldCarrier : SuiteOwnershipReceipt
sensibLawWorldCarrier = suiteOwnershipReceipt sensibLawOwner candidateWorldCarrier
  "SensibLaw/src/policy/world_model.py::sl.candidate_world_model.v0_1" false

itirGenericCompiler : SuiteOwnershipReceipt
itirGenericCompiler = suiteOwnershipReceipt itirSuiteOwner genericSourceCompiler
  "ITIR-suite/docs/planning/generic_world_model_compiler_convergence_20260716.md" false

tircorderNarrativeCarrier : SuiteOwnershipReceipt
tircorderNarrativeCarrier = suiteOwnershipReceipt tircorderOwner contestedNarrativeCarrier
  "tircorder-JOBBIE/docs/ontology.md" false

statiBakerTimeAxis : SuiteOwnershipReceipt
statiBakerTimeAxis = suiteOwnershipReceipt statiBakerOwner appendOnlyTimeAxis
  "StatiBaker/DESIGN.md" false

dashiProofBoundary : SuiteOwnershipReceipt
dashiProofBoundary = suiteOwnershipReceipt dashiOwner typedProofBoundary
  "DASHI/WorldModel/PredicateNormalWorldModelCore.agda" false

slrDiscourseOwner : SuiteOwnershipReceipt
slrDiscourseOwner = suiteOwnershipReceipt slrRuntimeOwner discourseReconstruction
  "tools/slr-discourse-reconstruct" false

------------------------------------------------------------------------
-- World constraints are an intersection surface, never another scalar score.
------------------------------------------------------------------------

record WorldConstraintFibre : Set where
  constructor worldConstraintFibre
  field
    discourseCandidateReference : String
    pnfConstraintReference : String
    roleConstraintReference : String
    sourceAttributionReference : String
    temporalConstraintReference : String
    narrativeAlternativeReference : String
    authorityConstraintReference : String
    residualReference : String
    compatible : Bool
    promotionReceiptReference : String

open WorldConstraintFibre public

record WorldConstrainedDiscourseCandidate : Set where
  constructor worldConstrainedDiscourseCandidate
  field
    discourseCandidateReference : String
    constraintFibre : WorldConstraintFibre
    candidateOnly : Bool
    truthPromoted : Bool

open WorldConstrainedDiscourseCandidate public

------------------------------------------------------------------------
-- Gold-labelled benchmark contract.
------------------------------------------------------------------------

record GoldDiscourseBenchmark : Set where
  constructor goldDiscourseBenchmark
  field
    noisySourceReference : String
    labelledSourceReference : String
    noisySourceDigestReference : String
    labelledSourceDigestReference : String
    reconstructedSpanReference : String
    speakerBoundaryPrecisionReference : String
    speakerBoundaryRecallReference : String
    quoteNestingAccuracyReference : String
    rolePreservationAccuracyReference : String
    falseCutRateReference : String
    hiddenSpliceRecoveryReference : String
    uncertaintyCalibrationReference : String
    residualFibreDeltaReference : String
    sourceRecoverabilityReference : String
    benchmarkPromotesTruth : Bool

open GoldDiscourseBenchmark public

abc730GoldBenchmarkPlan : GoldDiscourseBenchmark
abc730GoldBenchmarkPlan = goldDiscourseBenchmark
  "tools/slr-discourse-reconstruct/specimens/9-sept-8-03pm-unlabelled/source.txt"
  "tools/slr-discourse-reconstruct/specimens/abc730-2026-09-09-primary/source.txt"
  "specimens/9-sept-8-03pm-unlabelled/source.sha256"
  "specimens/abc730-2026-09-09-primary/source.sha256"
  "slr-discourse-spans-v4"
  "abc730-gold-benchmark.json:speaker_boundary.precision_milli"
  "abc730-gold-benchmark.json:speaker_boundary.recall_milli"
  "not-scored: official speaker labels are not independent quote/nesting gold annotation"
  "abc730-gold-benchmark.json:role_preservation.hard_speaker_role_preservation_milli"
  "abc730-gold-benchmark.json:speaker_boundary.false_cut_rate_milli"
  "abc730-gold-benchmark.json:hidden_splice.recovery_milli"
  "coverage-only: abc730-gold-benchmark.json:hidden_splice.uncertainty_recall_on_hard_misses_milli"
  "not-scored: requires aligned labelled-vs-unlabelled candidate fibres"
  "SLR_DISCOURSE_SPAN_INTEGRITY / abc730-gold-benchmark.json:source_recoverability"
  false

------------------------------------------------------------------------
-- Global roadmap state.
------------------------------------------------------------------------

data RoadmapState : Set where
  complete : RoadmapState
  frozenUnlessBenchmarkFails : RoadmapState
  implementedAwaitingRuntime : RoadmapState
  active : RoadmapState
  partial : RoadmapState
  next : RoadmapState

record SLRRoadmapCoordinate : Set where
  constructor slrRoadmapCoordinate
  field
    stageReference : String
    state : RoadmapState
    owner : SuiteOwner
    receiptReference : String

open SLRRoadmapCoordinate public

slrGlobalRoadmap : List SLRRoadmapCoordinate
slrGlobalRoadmap =
  slrRoadmapCoordinate "raw transcript/document custody" complete slrRuntimeOwner "source/projection sha256 + provenance" ∷
  slrRoadmapCoordinate "deterministic parse + SLR/PNF" complete slrRuntimeOwner "ABC + GWB + AU execution receipts" ∷
  slrRoadmapCoordinate "candidate cut arithmetic" frozenUnlessBenchmarkFails slrRuntimeOwner "legacy diagnostic scorer; reopen only on labelled failure" ∷
  slrRoadmapCoordinate "typed discourse fibre manifold" complete dashiOwner "SensibLawTranscriptBoundaryPNFWorldManifoldExact" ∷
  slrRoadmapCoordinate "lexical MUST/MAY counterfactuals" complete dashiOwner "SensibLawLexicalWildcardSubjectTransitionExact" ∷
  slrRoadmapCoordinate "typed role-transition admission" complete dashiOwner "SensibLawRoleTransitionManifoldExact" ∷
  slrRoadmapCoordinate "source-preserving span reconstruction" complete slrRuntimeOwner "slr-discourse-spans-v4" ∷
  slrRoadmapCoordinate "discourse-specific quality audit" complete dashiOwner "SensibLawDiscourseQualityAuditExact" ∷
  slrRoadmapCoordinate "SensibLaw CandidateWorldModel normalization parity" complete slrRuntimeOwner "ABC and GWB normalization_drift=false" ∷
  slrRoadmapCoordinate "cross-corpus SLR execution parity" complete slrRuntimeOwner "GWB 41,134 + AU 19,235 sentences; parity_failed=0; published=0" ∷
  slrRoadmapCoordinate "gold-labelled discourse benchmark" partial slrRuntimeOwner "speaker-turn benchmark executable; quote/nesting and full calibration remain open" ∷
  slrRoadmapCoordinate "canonical claim projection" complete slrRuntimeOwner "validated sentence-level canonical refs with ambiguity-preserving fused edges" ∷
  slrRoadmapCoordinate "same-source unique-phrase refinement" partial slrRuntimeOwner "available where source identity/unique phrase pays exact offsets; not required for every source" ∷
  slrRoadmapCoordinate "labelled-to-noisy subspan weld" complete slrRuntimeOwner "validated exact/bounded/unpaid distinction without forced closure" ∷
  slrRoadmapCoordinate "multi-hop labelled discourse path" complete slrRuntimeOwner "validated sentence 42 Wong -> Greber -> Husic and sentence 45 Shoebridge -> Leeser" ∷
  slrRoadmapCoordinate "claim-local fragment projection" complete slrRuntimeOwner "validated: 5 fragments / 4 claim-local / 1 intermediate; whole-claim extent=false" ∷
  slrRoadmapCoordinate "claim-local fragment residual inheritance" complete slrRuntimeOwner "validated: 10 obligations; intermediate fragment inherits none" ∷
  slrRoadmapCoordinate "fragment source/attribution evidence contraction" complete slrRuntimeOwner "validated: attribution_source_paid=4; claim truth and whole extent remain false" ∷
  slrRoadmapCoordinate "whole-claim span completion" partial slrRuntimeOwner "local fragments do not pay full canonical claim extents" ∷
  slrRoadmapCoordinate "GWB CandidateWorldModel corpus projection" complete slrRuntimeOwner "41,134 claims / 41,124 relations / provenance=10 / normalization_drift=false" ∷
  slrRoadmapCoordinate "reviewed Wikimedia-first world enrichment" complete dashiOwner "10 reviewed seeds -> 51 QID nodes / 850 property edges / 162 parent / 688 surrounding-related / post-follow parity" ∷
  slrRoadmapCoordinate "replayable cache + deterministic GWB handoff" complete slrRuntimeOwner "cache-only replay: 134 hits / 0 network; tar.xz SHA manifest; no raw/projected corpus text" ∷
  slrRoadmapCoordinate "GWB source-work identity residual contraction" complete slrRuntimeOwner "paid=2 / unpaid=8 / topic anchors=8 / runtime-resolved work identities=1 / normalization_drift=false" ∷
  slrRoadmapCoordinate "GWB claim-relative source-role atlas" implementedAwaitingRuntime dashiOwner "fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl / SLRGWBClaimRelativeSourceRoleAtlasExact" ∷
  slrRoadmapCoordinate "full world-constraint fibre integration" partial dashiOwner "generic fibre exists; domain consumers still attach/contract dimensions independently" ∷
  slrRoadmapCoordinate "consumer-specific world residual contraction" active sensibLawOwner "use reviewed Q/P/source-role evidence only against declared consumer obligations" ∷
  slrRoadmapCoordinate "claim/evidence graph projection" active sensibLawOwner "candidate claims/fragments carry graph identities and append-only evidence obligations" ∷
  slrRoadmapCoordinate "mechanism evidence snowball" active dashiOwner "Wikimedia-first, then broader Snowball only for surviving consumer debt" ∷
  slrRoadmapCoordinate "review/promote/abstain routing" complete sensibLawOwner "compatibility / adequacy / residual gates remain separate" ∷
  slrRoadmapCoordinate "ABC C029 policy/evaluative consumer adequacy" active dashiOwner "source attribution paid; implementation/incidence/counterfactual residuals remain" ∷
  slrRoadmapCoordinate "GWB canonical claim/evidence extraction" next slrRuntimeOwner "begin only after source-role attachment; adjacency/QID graph alone cannot manufacture claims" ∷
  []

------------------------------------------------------------------------
-- Cross-pollination laws.
------------------------------------------------------------------------

record SuiteConvergenceLaw : Set where
  constructor suiteConvergenceLaw
  field
    sensibLawOwnsCandidateSemanticCarrier : Bool
    itirOwnsGenericCompilationPath : Bool
    tircorderOwnsContestedNarrativeAlternatives : Bool
    statiBakerOwnsTemporalReplayAxis : Bool
    dashiOwnsTypedProposalPromotionBoundary : Bool
    slrOwnsDiscourseReconstruction : Bool
    sourceEvidenceMayDeepenSparseWorld : Bool
    benchmarkMayReopenFrozenHeuristics : Bool
    oneRepoMaySilentlyReplaceAnotherOwner : Bool

open SuiteConvergenceLaw public

canonicalSuiteConvergenceLaw : SuiteConvergenceLaw
canonicalSuiteConvergenceLaw = suiteConvergenceLaw true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data WorldConstraintIsScalarScore : Set where
data CandidateWorldModelIsWorldTruth : Set where
data StatiBakerObservedStateIsSemanticAuthority : Set where
data TiRCNarrativeAlternativeIsHistoricalFact : Set where
data BenchmarkImprovementPromotesClaimTruth : Set where
data ExternalEvidenceMayRewritePriorSourceState : Set where
data ParserHeuristicMayReopenWithoutBenchmarkFailure : Set where

worldConstraintIsNotScalar : WorldConstraintIsScalarScore → ⊥
worldConstraintIsNotScalar ()

candidateWorldModelIsNotWorldTruth : CandidateWorldModelIsWorldTruth → ⊥
candidateWorldModelIsNotWorldTruth ()

statiBakerObservationIsNotSemanticAuthority : StatiBakerObservedStateIsSemanticAuthority → ⊥
statiBakerObservationIsNotSemanticAuthority ()

tircNarrativeIsNotHistoricalFact : TiRCNarrativeAlternativeIsHistoricalFact → ⊥
tircNarrativeIsNotHistoricalFact ()

benchmarkDoesNotPromoteTruth : BenchmarkImprovementPromotesClaimTruth → ⊥
benchmarkDoesNotPromoteTruth ()

externalEvidenceDoesNotRewritePriorState : ExternalEvidenceMayRewritePriorSourceState → ⊥
externalEvidenceDoesNotRewritePriorState ()

parserHeuristicRequiresBenchmarkFailureToReopen : ParserHeuristicMayReopenWithoutBenchmarkFailure → ⊥
parserHeuristicRequiresBenchmarkFailureToReopen ()

------------------------------------------------------------------------
-- Existing-owner anchors prove this owner composes rather than forks them.
------------------------------------------------------------------------

predicateNormalBoundaryAnchor :
  (model : PNW.PredicateNormalWorldModelCore) →
  (observation : PNW.Observation model) →
  PNW.PredicateNormalProposalBoundary model observation →
  PNW.PredicateNormalProposalBoundary model observation
predicateNormalBoundaryAnchor model observation boundary = boundary

sparseWorldBoundaryAnchor : Sparse.SparseWorldBoundary
sparseWorldBoundaryAnchor = Sparse.canonicalSparseWorldBoundary

discourseQualityBoundaryAnchor : Quality.DiscourseQualityBoundary
discourseQualityBoundaryAnchor = Quality.canonicalDiscourseQualityBoundary

ibrahimSourceGrammarAnchor : Ibrahim.SnowballAttributionBoundary
ibrahimSourceGrammarAnchor = Ibrahim.canonicalSnowballAttributionBoundary

suiteArchitectureBoundaryAnchor : ITIRSL.ArchitectureAuthorityBits
suiteArchitectureBoundaryAnchor = ITIRSL.canonicalArchitectureAuthorityBits
