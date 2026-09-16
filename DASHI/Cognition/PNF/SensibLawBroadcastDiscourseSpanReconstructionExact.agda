module DASHI.Cognition.PNF.SensibLawBroadcastDiscourseSpanReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold
import DASHI.Cognition.PNF.SensibLawBroadcastDiscourseGraphCompilerExact as Graph
import DASHI.Cognition.PNF.SensibLawRoleTransitionManifoldExact as Role
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Residual

------------------------------------------------------------------------
-- Broadcast discourse span reconstruction.
--
-- Runtime v4 consumes the independent role-transition manifold. A Pareto
-- singleton is necessary but not sufficient for a hard cut: the selected
-- discourse interpretation must be compatible with actor/patient/predicate/
-- clause continuations for that consumer. Coordination remains observable but
-- is not itself a hard veto. Quote handoffs may retain content-clause crossing.
------------------------------------------------------------------------

data SpanBoundaryDisposition : Set where
  preserveOriginalSentence : SpanBoundaryDisposition
  candidateSpeakerCut : SpanBoundaryDisposition
  candidateQuoteHandoff : SpanBoundaryDisposition
  roleCompatibilityVeto : SpanBoundaryDisposition
  unresolvedBoundary : SpanBoundaryDisposition

record RoleCompatibilityCutReceipt : Set where
  constructor roleCompatibilityCutReceipt
  field
    crossingRoleReference : String
    actorCrossingReference : String
    patientCrossingReference : String
    predicateAuxCrossingReference : String
    clauseCrossingReference : String
    coordinationCrossingReference : String
    projectionReference : String
    compatibilityRuleReference : String
    admissibleReference : String

open RoleCompatibilityCutReceipt public

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
    roleCompatibilityReceiptReference : String
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
    roleManifoldReference : String
    reconstructionSchema : String
    spans : List ReconstructedDiscourseSpan
    hardCutRuleReference : String
    roleCompatibilityGateReference : String
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
    speakerVetoActorCrossing : Bool
    speakerVetoPatientCrossing : Bool
    speakerVetoPredicateAuxCrossing : Bool
    speakerVetoClauseCrossing : Bool
    quoteVetoActorCrossing : Bool
    quoteVetoPatientCrossing : Bool
    quoteVetoPredicateAuxCrossing : Bool
    quoteMayRetainClauseCrossing : Bool
    coordinationCrossingAloneMayRemainLive : Bool
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
    true true true true
    true true true true
    true
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

data SingletonParetoOverridesRoleManifold : Set where
singletonParetoDoesNotOverrideRoleManifold : SingletonParetoOverridesRoleManifold → ⊥
singletonParetoDoesNotOverrideRoleManifold ()

data SpeakerCutMaySeverCoreRole : Set where
speakerCutMayNotSeverCoreRole : SpeakerCutMaySeverCoreRole → ⊥
speakerCutMayNotSeverCoreRole ()

data CoordinationCrossingMustBlockSpeaker : Set where
coordinationCrossingNeedNotBlockSpeaker : CoordinationCrossingMustBlockSpeaker → ⊥
coordinationCrossingNeedNotBlockSpeaker ()

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

roleBoundaryAnchor : Role.RoleTransitionBoundary
roleBoundaryAnchor = Role.canonicalRoleTransitionBoundary

roleCompatibilityAnchor : Role.DiscourseRoleCompatibility
roleCompatibilityAnchor = Role.canonicalDiscourseRoleCompatibility

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
    singletonParetoStillNeedsRoleCompatibility : Bool
    speakerCoreRolesAreHardVetoes : Bool
    predicateAuxContinuationIsHardVeto : Bool
    coordinationAloneIsNotHardVeto : Bool
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
    true true true true true true true true true true
