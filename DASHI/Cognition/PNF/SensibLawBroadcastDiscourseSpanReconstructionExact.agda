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
-- The runtime projection is downstream of the PNF/world manifold. A Pareto
-- singleton is necessary but not sufficient for a hard cut: the selected cut
-- must also preserve the core PNF role relations appropriate to its discourse
-- kind. Speaker cuts may not sever subject/object/clause relations. Quote
-- handoffs may retain a clause/content attachment, but may not sever actor or
-- patient relations. This keeps parser topology as a typed veto rather than a
-- scalar penalty.
------------------------------------------------------------------------

data SpanBoundaryDisposition : Set where
  preserveOriginalSentence : SpanBoundaryDisposition
  candidateSpeakerCut : SpanBoundaryDisposition
  candidateQuoteHandoff : SpanBoundaryDisposition
  pnfStructuralVeto : SpanBoundaryDisposition
  unresolvedBoundary : SpanBoundaryDisposition

record PNFStructuralCutReceipt : Set where
  constructor pnfStructuralCutReceipt
  field
    subjectCrossings : Nat
    objectCrossings : Nat
    clauseCrossings : Nat
    coordinationCrossings : Nat
    projectionReference : String
    structuralRuleReference : String
    admissibleReference : String

open PNFStructuralCutReceipt public

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
    pnfStructuralReceiptReference : String
    speakerCandidateReference : String
    speakerStatusReference : String
    claimReference : String
    candidateOnly : Bool

open ReconstructedDiscourseSpan public

record ParagraphTopologyReceipt : Set where
  constructor paragraphTopologyReceipt
  field
    sourceParagraphReference : String
    reconstructedParagraphReference : String
    originalSeparatorCountReference : String
    insertedBoundaryCountReference : String
    originalSeparatorsPreserved : Bool
    reconstructionOnlyAddsBoundarySeparators : Bool

open ParagraphTopologyReceipt public

record SourceRecoverabilityReceipt : Set where
  constructor sourceRecoverabilityReceipt
  field
    sourceByteCount : Nat
    reconstructedByteCount : Nat
    insertedNewlineCount : Nat
    sourceDoubleNewlineCount : Nat
    reconstructedDoubleNewlineCount : Nat
    runtimeSchemaReference : String
    sourceRecoverableByDeletingInsertedNewlines : Bool
    reconstructedDidNotShrink : Bool
    paragraphSeparatorsDidNotDecrease : Bool

open SourceRecoverabilityReceipt public

record SpanReconstructionReceipt : Set where
  constructor spanReconstructionReceipt
  field
    sourceReference : String
    graphReference : String
    reconstructionSchema : String
    spans : List ReconstructedDiscourseSpan
    hardCutRuleReference : String
    pnfStructuralGateReference : String
    unresolvedBoundaryReference : String
    sourceCoverageReference : String
    paragraphTopologyReference : String
    sourceRecoverabilityReference : String
    replayReference : String

open SpanReconstructionReceipt public

------------------------------------------------------------------------
-- Narrow executable policy.
------------------------------------------------------------------------

record CandidateHardCutPolicy : Set where
  constructor candidateHardCutPolicy
  field
    requiresRankOne : Bool
    requiresSingletonPareto : Bool
    speakerRequiresZeroSubjectCrossings : Bool
    speakerRequiresZeroObjectCrossings : Bool
    speakerRequiresZeroClauseCrossings : Bool
    quoteRequiresZeroSubjectCrossings : Bool
    quoteRequiresZeroObjectCrossings : Bool
    quoteMayRetainClauseCrossing : Bool
    permitsSpeakerProjection : Bool
    permitsQuoteProjection : Bool
    permitsNestingProjection : Bool
    permitsASRProjection : Bool
    permitsRhetoricalProjection : Bool
    unresolvedFrontCreatesHardCut : Bool

canonicalCandidateHardCutPolicy : CandidateHardCutPolicy
canonicalCandidateHardCutPolicy =
  candidateHardCutPolicy
    true true
    true true true
    true true true
    true true false false false false

------------------------------------------------------------------------
-- Raw versus reconstructed PNF comparison.
------------------------------------------------------------------------

record PNFRunSummary : Set where
  constructor pnfRunSummary
  field
    runReference : String
    sentenceRowCount : Nat
    paragraphRowCount : Nat
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
    paragraphTopologyDeltaReference : String
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

data SingletonParetoOverridesPNFStructure : Set where
singletonParetoDoesNotOverridePNFStructure : SingletonParetoOverridesPNFStructure → ⊥
singletonParetoDoesNotOverridePNFStructure ()

data SpeakerCutMaySeverCorePNFRole : Set where
speakerCutMayNotSeverCorePNFRole : SpeakerCutMaySeverCorePNFRole → ⊥
speakerCutMayNotSeverCorePNFRole ()

data QuoteClauseCrossingMeansSpeakerCut : Set where
quoteClauseCrossingDoesNotMeanSpeakerCut : QuoteClauseCrossingMeansSpeakerCut → ⊥
quoteClauseCrossingDoesNotMeanSpeakerCut ()

data LowerResidualDensityProvesSemanticTruth : Set where
lowerResidualDensityDoesNotProveSemanticTruth : LowerResidualDensityProvesSemanticTruth → ⊥
lowerResidualDensityDoesNotProveSemanticTruth ()

data ReconstructionMayEraseUnresolvedBoundary : Set where
reconstructionMayNotEraseUnresolvedBoundary : ReconstructionMayEraseUnresolvedBoundary → ⊥
reconstructionMayNotEraseUnresolvedBoundary ()

data ReconstructionMayCollapseSourceParagraphTopology : Set where
reconstructionMayNotCollapseSourceParagraphTopology : ReconstructionMayCollapseSourceParagraphTopology → ⊥
reconstructionMayNotCollapseSourceParagraphTopology ()

data NonNewlineMutationMayPassIntegrityGate : Set where
nonNewlineMutationMayNotPassIntegrityGate : NonNewlineMutationMayPassIntegrityGate → ⊥
nonNewlineMutationMayNotPassIntegrityGate ()

data StaleSchemaMayPassIntegrityGate : Set where
staleSchemaMayNotPassIntegrityGate : StaleSchemaMayPassIntegrityGate → ⊥
staleSchemaMayNotPassIntegrityGate ()

data ParagraphCountEqualityProvesSemanticEquivalence : Set where
paragraphCountEqualityDoesNotProveSemanticEquivalence : ParagraphCountEqualityProvesSemanticEquivalence → ⊥
paragraphCountEqualityDoesNotProveSemanticEquivalence ()

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
    originalParagraphTopologyPreserved : Bool
    candidateCutsOnlyAddSeparators : Bool
    sourceRecoverabilityCheckedAtRuntime : Bool
    staleSchemaFailsClosed : Bool
    nonNewlineMutationFailsClosed : Bool
    unresolvedParetoFrontsRemainUnsplit : Bool
    singletonParetoStillNeedsPNFStructuralAdmission : Bool
    speakerCorePNFRelationsAreHardVetoes : Bool
    quoteClauseAttachmentMayRemainLive : Bool
    speakerIdentityIndependentOfCutProjection : Bool
    rerunPNFIsRequiredForComparison : Bool
    lowerResidualIsDiagnosticNotTruth : Bool
    paragraphEqualityIsDiagnosticNotTruth : Bool
    claimGraphRepairIsDownstream : Bool

canonicalSpanReconstructionBoundary : SpanReconstructionBoundary
canonicalSpanReconstructionBoundary =
  spanReconstructionBoundary
    true true true true true true true true
    true true true true true true true true
