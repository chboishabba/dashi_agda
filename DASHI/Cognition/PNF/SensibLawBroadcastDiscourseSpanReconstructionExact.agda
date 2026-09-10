module DASHI.Cognition.PNF.SensibLawBroadcastDiscourseSpanReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold
import DASHI.Cognition.PNF.SensibLawBroadcastDiscourseGraphCompilerExact as Graph
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Residual

------------------------------------------------------------------------
-- Broadcast discourse span reconstruction.
--
-- This owner is downstream of the PNF/world boundary manifold.  It does not
-- rewrite the source transcript.  It emits a separate candidate segmentation
-- plus a provenance ledger, keeping unresolved manifold boundaries intact.
------------------------------------------------------------------------

data SpanBoundaryDisposition : Set where
  preserveOriginalSentence : SpanBoundaryDisposition
  candidateSpeakerCut : SpanBoundaryDisposition
  candidateQuoteHandoff : SpanBoundaryDisposition
  unresolvedBoundary : SpanBoundaryDisposition

record ReconstructedDiscourseSpan : Set where
  constructor reconstructedDiscourseSpan
  field
    spanReference : String
    sourceSha256 : String
    sourceSentenceReference : String
    sourceCharStartReference : String
    sourceCharEndReference : String
    boundaryBeforeReference : String
    boundaryDisposition : SpanBoundaryDisposition
    paretoFrontReference : String
    retainedResidualReference : String
    speakerCandidateReference : String
    speakerStatusReference : String
    claimReference : String
    candidateOnly : Bool

open ReconstructedDiscourseSpan public

record SpanReconstructionReceipt : Set where
  constructor spanReconstructionReceipt
  field
    sourceReference : String
    graphReference : String
    reconstructionSchema : String
    spans : List ReconstructedDiscourseSpan
    hardCutRuleReference : String
    unresolvedBoundaryReference : String
    sourceCoverageReference : String
    replayReference : String

open SpanReconstructionReceipt public

------------------------------------------------------------------------
-- Narrow executable policy.
--
-- Runtime v1 permits a candidate hard cut only for a rank-1 singleton Pareto
-- projection whose discourse kind is speaker or quote.  This is an engineering
-- projection for the comparison experiment, not a semantic theorem.
------------------------------------------------------------------------

record CandidateHardCutPolicy : Set where
  constructor candidateHardCutPolicy
  field
    requiresRankOne : Bool
    requiresSingletonPareto : Bool
    permitsSpeakerProjection : Bool
    permitsQuoteProjection : Bool
    permitsNestingProjection : Bool
    permitsASRProjection : Bool
    permitsRhetoricalProjection : Bool
    unresolvedFrontCreatesHardCut : Bool

canonicalCandidateHardCutPolicy : CandidateHardCutPolicy
canonicalCandidateHardCutPolicy =
  candidateHardCutPolicy true true true true false false false false

------------------------------------------------------------------------
-- Raw versus reconstructed PNF comparison.
------------------------------------------------------------------------

record PNFRunSummary : Set where
  constructor pnfRunSummary
  field
    runReference : String
    sentenceRowCount : Nat
    residualRowCount : Nat
    residualTotal : Nat
    candidateRowCount : Nat
    symbolRowCount : Nat
    residualDensityReference : String
    runtimeReceiptReference : String

open PNFRunSummary public

record RawReconstructedPNFComparison : Set where
  constructor rawReconstructedPNFComparison
  field
    rawRun : PNFRunSummary
    reconstructedRun : PNFRunSummary
    residualDeltaReference : String
    residualDensityDeltaReference : String
    attributionAmbiguityDeltaReference : String
    falseJoinDeltaReference : String
    worldModelMismatchDeltaReference : String
    comparisonOnly : Bool

open RawReconstructedPNFComparison public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CandidateSpanIsCanonicalTranscript : Set where
candidateSpanDoesNotBecomeCanonicalTranscript : CandidateSpanIsCanonicalTranscript → ⊥
candidateSpanDoesNotBecomeCanonicalTranscript ()

data SingletonParetoVerifiesSpeaker : Set where
singletonParetoDoesNotVerifySpeaker : SingletonParetoVerifiesSpeaker → ⊥
singletonParetoDoesNotVerifySpeaker ()

data LowerResidualDensityProvesSemanticTruth : Set where
lowerResidualDensityDoesNotProveSemanticTruth : LowerResidualDensityProvesSemanticTruth → ⊥
lowerResidualDensityDoesNotProveSemanticTruth ()

data ReconstructionMayEraseUnresolvedBoundary : Set where
reconstructionMayNotEraseUnresolvedBoundary : ReconstructionMayEraseUnresolvedBoundary → ⊥
reconstructionMayNotEraseUnresolvedBoundary ()

data ComparisonMayPromoteWorldClaim : Set where
comparisonMayNotPromoteWorldClaim : ComparisonMayPromoteWorldClaim → ⊥
comparisonMayNotPromoteWorldClaim ()

------------------------------------------------------------------------
-- Existing owners remain semantic authority.
------------------------------------------------------------------------

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary

graphBoundaryAnchor : Graph.BroadcastDiscourseGraphBoundary
graphBoundaryAnchor = Graph.canonicalBroadcastDiscourseGraphBoundary

residualBoundaryAnchor : Residual.SemanticResidualBoundary
residualBoundaryAnchor = Residual.canonicalSemanticResidualBoundary

record SpanReconstructionBoundary : Set where
  constructor spanReconstructionBoundary
  field
    sourceTranscriptRemainsImmutable : Bool
    reconstructedTextIsSeparateProjection : Bool
    unresolvedParetoFrontsRemainUnsplit : Bool
    speakerIdentityIndependentOfCutProjection : Bool
    rerunPNFIsRequiredForComparison : Bool
    lowerResidualIsDiagnosticNotTruth : Bool
    claimGraphRepairIsDownstream : Bool

canonicalSpanReconstructionBoundary : SpanReconstructionBoundary
canonicalSpanReconstructionBoundary =
  spanReconstructionBoundary true true true true true true true
