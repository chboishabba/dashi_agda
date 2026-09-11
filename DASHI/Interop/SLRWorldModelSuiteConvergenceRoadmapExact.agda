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

------------------------------------------------------------------------
-- SLR / WORLD-MODEL SUITE CONVERGENCE ROADMAP
--
-- This owner records the cross-repo division of labour discovered across:
--   SensibLaw      : generic CandidateWorldModel / review / promotion surface
--   ITIR-suite     : generic source -> span/PNF -> world-model compiler
--   TiRCorder      : contested event/narrative interpretation and provenance
--   StatiBaker     : append-only temporal state / replay / drift surface
--   DASHI          : typed proposal, promotion, sparse-world and proof boundaries
--
-- None of these is a competing terminal architecture.  SLR consumes them as
-- orthogonal carriers and constraints.
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
sensibLawWorldCarrier =
  suiteOwnershipReceipt sensibLawOwner candidateWorldCarrier
    "SensibLaw/src/policy/world_model.py::sl.candidate_world_model.v0_1"
    false

itirGenericCompiler : SuiteOwnershipReceipt
itirGenericCompiler =
  suiteOwnershipReceipt itirSuiteOwner genericSourceCompiler
    "ITIR-suite/docs/planning/generic_world_model_compiler_convergence_20260716.md"
    false

tircorderNarrativeCarrier : SuiteOwnershipReceipt
tircorderNarrativeCarrier =
  suiteOwnershipReceipt tircorderOwner contestedNarrativeCarrier
    "tircorder-JOBBIE/docs/ontology.md"
    false

statiBakerTimeAxis : SuiteOwnershipReceipt
statiBakerTimeAxis =
  suiteOwnershipReceipt statiBakerOwner appendOnlyTimeAxis
    "StatiBaker/DESIGN.md"
    false

dashiProofBoundary : SuiteOwnershipReceipt
dashiProofBoundary =
  suiteOwnershipReceipt dashiOwner typedProofBoundary
    "DASHI/WorldModel/PredicateNormalWorldModelCore.agda"
    false

slrDiscourseOwner : SuiteOwnershipReceipt
slrDiscourseOwner =
  suiteOwnershipReceipt slrRuntimeOwner discourseReconstruction
    "tools/slr-discourse-reconstruct"
    false

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
abc730GoldBenchmarkPlan =
  goldDiscourseBenchmark
    "tools/slr-discourse-reconstruct/specimens/9-sept-8-03pm-unlabelled/source.txt"
    "tools/slr-discourse-reconstruct/specimens/abc730-2026-09-09-primary/source.txt"
    "specimens/9-sept-8-03pm-unlabelled/source.sha256"
    "specimens/abc730-2026-09-09-primary/source.sha256"
    "slr-discourse-spans-v4"
    "pending: speaker-boundary precision"
    "pending: speaker-boundary recall"
    "pending: quote/nesting accuracy"
    "pending: typed-role preservation accuracy"
    "pending: false-cut rate"
    "pending: hidden-speaker-splice recovery"
    "pending: speaker uncertainty calibration"
    "pending: residual-fibre width before/after source evidence"
    "SLR_DISCOURSE_SPAN_INTEGRITY"
    false

------------------------------------------------------------------------
-- Global roadmap state.
------------------------------------------------------------------------

data RoadmapState : Set where
  complete : RoadmapState
  frozenUnlessBenchmarkFails : RoadmapState
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
  slrRoadmapCoordinate "raw transcript custody" complete slrRuntimeOwner "source sha256 + provenance" ∷
  slrRoadmapCoordinate "deterministic parse + SLR/PNF" complete slrRuntimeOwner "parser.tsv + pnf receipt" ∷
  slrRoadmapCoordinate "candidate cut arithmetic" frozenUnlessBenchmarkFails slrRuntimeOwner "legacy diagnostic scorer" ∷
  slrRoadmapCoordinate "typed discourse fibre manifold" complete dashiOwner "SensibLawTranscriptBoundaryPNFWorldManifoldExact" ∷
  slrRoadmapCoordinate "lexical MUST/MAY counterfactuals" complete dashiOwner "SensibLawLexicalWildcardSubjectTransitionExact" ∷
  slrRoadmapCoordinate "typed role-transition admission" complete dashiOwner "SensibLawRoleTransitionManifoldExact" ∷
  slrRoadmapCoordinate "source-preserving span reconstruction" complete slrRuntimeOwner "slr-discourse-spans-v4" ∷
  slrRoadmapCoordinate "discourse-specific quality audit" complete dashiOwner "SensibLawDiscourseQualityAuditExact" ∷
  slrRoadmapCoordinate "gold-labelled discourse benchmark" next slrRuntimeOwner "ABC730 labelled-vs-unlabelled benchmark" ∷
  slrRoadmapCoordinate "full world-constraint fibre integration" active dashiOwner "WorldConstraintFibre" ∷
  slrRoadmapCoordinate "claim/evidence graph projection" active sensibLawOwner "CandidateWorldModel claims+relations+provenance" ∷
  slrRoadmapCoordinate "mechanism evidence snowball" active dashiOwner "ABC730 Ibrahim/Snowball policy owners" ∷
  slrRoadmapCoordinate "policy/evaluative consumer" next sensibLawOwner "review/promote/abstain consumer" ∷
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
canonicalSuiteConvergenceLaw =
  suiteConvergenceLaw true true true true true true true true false

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

statiBakerObservationIsNotSemanticAuthority :
  StatiBakerObservedStateIsSemanticAuthority → ⊥
statiBakerObservationIsNotSemanticAuthority ()

tircNarrativeIsNotHistoricalFact : TiRCNarrativeAlternativeIsHistoricalFact → ⊥
tircNarrativeIsNotHistoricalFact ()

benchmarkDoesNotPromoteTruth : BenchmarkImprovementPromotesClaimTruth → ⊥
benchmarkDoesNotPromoteTruth ()

externalEvidenceDoesNotRewritePriorState :
  ExternalEvidenceMayRewritePriorSourceState → ⊥
externalEvidenceDoesNotRewritePriorState ()

parserHeuristicRequiresBenchmarkFailureToReopen :
  ParserHeuristicMayReopenWithoutBenchmarkFailure → ⊥
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

ibrahimSourceGrammarAnchor : Ibrahim.SourceCoordinateBoundary
ibrahimSourceGrammarAnchor = Ibrahim.canonicalSourceCoordinateBoundary
