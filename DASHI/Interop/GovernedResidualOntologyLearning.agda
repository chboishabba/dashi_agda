module DASHI.Interop.GovernedResidualOntologyLearning where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Interop.ExternalContextSafetyBoundary as Safety
import DASHI.Interop.SpectralOperatorShapeCore as SpectralShape
import DASHI.Interop.WikidataSpectralPressureBridge as Pressure

------------------------------------------------------------------------
-- Governed residual ontology learning.
--
-- This is the formal boundary for the "Wiki solves itself over time"
-- workflow.  A runtime may calculate feature vectors, residual graphs, and
-- spectral clusters from revision-pinned observations.  This module records
-- the safety laws for consuming those outputs: only independently reviewed
-- conforming members may refine an empirical invariant; raw resemblance is
-- context-gated; and split/disjoint/new-class outputs remain proposals.
--
-- It deliberately does not implement a graph solver, peer statistics, P31 /
-- P279 closure, or ontology mutation.

------------------------------------------------------------------------
-- A domain invariant has distinct normative, empirical, conditional, and
-- legacy/noise surfaces.  The latter three are versioned observations, not a
-- majority vote which can override the policy model.

record DomainInvariantSnapshot : Set where
  constructor domainInvariantSnapshot
  field
    domainReference : String
    revisionReference : String
    policyModelReference : String
    trustedCohortReference : String
    normativeFeatureReference : String
    empiricalFeatureReference : String
    conditionalVariationReference : String
    legacyOrNoiseReference : String
    coverageReference : String
    policyAnchored : Bool
    policyAnchoredIsTrue : policyAnchored ≡ true
    diagnosticOnly : Bool
    diagnosticOnlyIsTrue : diagnosticOnly ≡ true

open DomainInvariantSnapshot public

------------------------------------------------------------------------
-- Review, rather than resemblance, controls training/cohort admission.

data CohortAdmissionDisposition : Set where
  confirmedModelConformant : CohortAdmissionDisposition
  confirmedConformantAfterSplit : CohortAdmissionDisposition
  confirmedConformantAfterRepair : CohortAdmissionDisposition
  held : CohortAdmissionDisposition
  ambiguous : CohortAdmissionDisposition
  unresolved : CohortAdmissionDisposition
  manualReconstruction : CohortAdmissionDisposition
  coverageIncomplete : CohortAdmissionDisposition

contributesToEmpiricalInvariant :
  CohortAdmissionDisposition →
  Bool
contributesToEmpiricalInvariant confirmedModelConformant = true
contributesToEmpiricalInvariant confirmedConformantAfterSplit = true
contributesToEmpiricalInvariant confirmedConformantAfterRepair = true
contributesToEmpiricalInvariant held = false
contributesToEmpiricalInvariant ambiguous = false
contributesToEmpiricalInvariant unresolved = false
contributesToEmpiricalInvariant manualReconstruction = false
contributesToEmpiricalInvariant coverageIncomplete = false

heldDoesNotTrainInvariant :
  contributesToEmpiricalInvariant held ≡ false
heldDoesNotTrainInvariant = refl

unresolvedDoesNotTrainInvariant :
  contributesToEmpiricalInvariant unresolved ≡ false
unresolvedDoesNotTrainInvariant = refl

coverageIncompleteDoesNotTrainInvariant :
  contributesToEmpiricalInvariant coverageIncomplete ≡ false
coverageIncompleteDoesNotTrainInvariant = refl

record TrustedConformingMember : Set where
  constructor trustedConformingMember
  field
    entityReference : String
    entityRevisionReference : String
    independentReviewReference : String
    disposition : CohortAdmissionDisposition
    admittedToInvariant : Bool
    admittedToInvariantMatchesDisposition :
      admittedToInvariant ≡ contributesToEmpiricalInvariant disposition
    localRoleReceiptReference : String
    automaticAdmission : Bool
    automaticAdmissionIsFalse : automaticAdmission ≡ false

open TrustedConformingMember public

record InvariantContributionReceipt : Set where
  constructor invariantContributionReceipt
  field
    member : TrustedConformingMember
    priorInvariant : DomainInvariantSnapshot
    admittedFeatureReference : String
    conditionalBranchReference : String
    exclusionReasonReference : String
    independentReviewRequired : Bool
    independentReviewRequiredIsTrue : independentReviewRequired ≡ true
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true

open InvariantContributionReceipt public

record InvariantRevisionReceipt : Set where
  constructor invariantRevisionReceipt
  field
    previousInvariant : DomainInvariantSnapshot
    nextInvariant : DomainInvariantSnapshot
    contributionReference : String
    strengthenedFeatureReference : String
    weakenedFeatureReference : String
    newConditionalBranchReference : String
    proposedCohortSplitReference : String
    reviewerAuthorityReference : String
    automaticOntologyMutation : Bool
    automaticOntologyMutationIsFalse : automaticOntologyMutation ≡ false

open InvariantRevisionReceipt public

------------------------------------------------------------------------
-- Rich residual patterns are retained as typed evidence.  The finite
-- diagonal pressure is only one coordinate and never replaces this record.

data ResidualFeatureKind : Set where
  typedMissingness : ResidualFeatureKind
  typedExcess : ResidualFeatureKind
  cardinalityDeviation : ResidualFeatureKind
  qualifierDeviation : ResidualFeatureKind
  temporalDeviation : ResidualFeatureKind
  ancestryDeviation : ResidualFeatureKind
  disjointnessEvidence : ResidualFeatureKind

data ContextualComparisonStatus : Set where
  contextAdmissible : ContextualComparisonStatus
  contextMasked : ContextualComparisonStatus
  contextUnknown : ContextualComparisonStatus
  contextInadmissible : ContextualComparisonStatus

record ResidualFeatureReceipt : Set where
  constructor residualFeatureReceipt
  field
    focalEntityReference : String
    featureKind : ResidualFeatureKind
    sourceAndCoverageReference : String
    localRoleReceiptReference : String
    comparisonStatus : ContextualComparisonStatus
    featureReference : String
    diagnosticOnly : Bool
    diagnosticOnlyIsTrue : diagnosticOnly ≡ true

open ResidualFeatureReceipt public

data ResidualEdgeKind : Set where
  compatibleSimilarityEdge : ResidualEdgeKind
  incompatibleOrDisjointEdge : ResidualEdgeKind
  maskedAnalogyEdge : ResidualEdgeKind
  unknownCoverageEdge : ResidualEdgeKind

edgeKindForContext :
  ContextualComparisonStatus →
  ResidualEdgeKind
edgeKindForContext contextAdmissible = compatibleSimilarityEdge
edgeKindForContext contextMasked = maskedAnalogyEdge
edgeKindForContext contextUnknown = unknownCoverageEdge
edgeKindForContext contextInadmissible = maskedAnalogyEdge

inadmissibleContextIsMasked :
  edgeKindForContext contextInadmissible ≡ maskedAnalogyEdge
inadmissibleContextIsMasked = refl

unknownContextIsNotSimilarity :
  edgeKindForContext contextUnknown ≡ unknownCoverageEdge
unknownContextIsNotSimilarity = refl

------------------------------------------------------------------------
-- A solver result is a supplied, receipt-backed diagnostic.  Its permissible
-- outputs describe possible ontology repairs, never edits or truth.

data SpectralPatternFinding : Set where
  nearbyExistingClass : SpectralPatternFinding
  stableSplitCandidate : SpectralPatternFinding
  disjointnessCandidate : SpectralPatternFinding
  bridgeSuperclassCandidate : SpectralPatternFinding
  newAbstractClassCandidate : SpectralPatternFinding
  legitimateExceptionCandidate : SpectralPatternFinding
  misclassificationCandidate : SpectralPatternFinding
  rejectedContextualAnalogy : SpectralPatternFinding

record ContextGatedSpectralSolveReceipt : Set where
  constructor contextGatedSpectralSolveReceipt
  field
    invariant : DomainInvariantSnapshot
    graphInputReference : String
    solverInputReceiptReference : String
    solverOutputReceiptReference : String
    operatorShape : SpectralShape.SpectralOperatorShapeReceipt
    pressureWitnessReference : String
    finding : SpectralPatternFinding
    contextualStatus : ContextualComparisonStatus
    findingReference : String
    onlyAdmissibleEdgesEnterSimilaritySolve : Bool
    onlyAdmissibleEdgesEnterSimilaritySolveIsTrue :
      onlyAdmissibleEdgesEnterSimilaritySolve ≡ true
    automaticClassAssignment : Bool
    automaticClassAssignmentIsFalse : automaticClassAssignment ≡ false
    automaticOntologyMutation : Bool
    automaticOntologyMutationIsFalse : automaticOntologyMutation ≡ false
    truthAuthority : Bool
    truthAuthorityIsFalse : truthAuthority ≡ false

open ContextGatedSpectralSolveReceipt public

------------------------------------------------------------------------
-- A runtime may legitimately report a rejected finding as either an
-- inadmissible domain/range comparison or a deliberately masked analogy.  The
-- required outcome is therefore carried by a separate receipt, not assumed of
-- arbitrary solver output.

record RejectedAnalogyReceipt : Set where
  constructor rejectedAnalogyReceipt
  field
    solve : ContextGatedSpectralSolveReceipt
    solveFindingIsRejected : finding solve ≡ rejectedContextualAnalogy
    statusIsInadmissibleOrMasked :
      contextualStatus solve ≡ contextInadmissible
      ⊎
      contextualStatus solve ≡ contextMasked
    noClassAssignment : automaticClassAssignment solve ≡ false
    noOntologyMutation : automaticOntologyMutation solve ≡ false

open RejectedAnalogyReceipt public

------------------------------------------------------------------------
-- Ontology-class merge pressure.
--
-- A merge is not the positive-edge dual of a split.  Residual-geometry
-- convergence can generate a candidate, but direct class replacement is only
-- reviewable after independent normative, typing, substitutability,
-- conditional-branch, impact, and provenance checks.

data NormativeCompatibility : Set where
  normativelyEquivalent : NormativeCompatibility
  leftSubsumesRight : NormativeCompatibility
  rightSubsumesLeft : NormativeCompatibility
  conditionallyEquivalent : NormativeCompatibility
  historicallyDistinct : NormativeCompatibility
  normativelyIncompatible : NormativeCompatibility
  normativelyUnderspecified : NormativeCompatibility

data MergeMode : Set where
  exactDuplicateMerge : MergeMode
  subsumptionMerge : MergeMode
  mergeUnderNewAbstraction : MergeMode
  sharedSuperclassOnly : MergeMode
  bridgeClassPreferred : MergeMode
  conditionalDistinctionPreserved : MergeMode
  historicalAliasOnly : MergeMode
  mergeBlocked : MergeMode
  mergeInsufficientCoverage : MergeMode

data MergeDisposition : Set where
  checkedMergeReviewable : MergeDisposition
  bridgeClassReviewPreferred : MergeDisposition
  sharedSuperclassReviewPreferred : MergeDisposition
  conditionalDistinctionReviewPreserved : MergeDisposition
  heldForMergeEvidence : MergeDisposition
  contradictoryMergeCandidate : MergeDisposition
  insufficientMergeCoverage : MergeDisposition

-- This is the candidate-generation object emitted by a residual solver.  Its
-- fields retain the evidence necessary to distinguish "no observed boundary"
-- from "safe to erase a boundary".
record OntologyMergeCandidate : Set where
  constructor ontologyMergeCandidate
  field
    leftClassReference : String
    rightClassReference : String
    proposedTargetClassReference : String
    proposedNewClassReference : String
    proposedMode : MergeMode
    normativeCompatibility : NormativeCompatibility
    empiricalGeometryReference : String
    crossClassPositiveEdgeReference : String
    crossClassNegativeEdgeReference : String
    contextMaskReference : String
    conditionalDistinctionReference : String
    relationSubstitutabilityReference : String
    downstreamImpactReference : String
    provenanceTransferPlanReference : String
    counterevidenceReference : String
    coverageReference : String
    candidateIsReviewOnly : Bool
    candidateIsReviewOnlyIsTrue : candidateIsReviewOnly ≡ true
    candidateHasMergeAuthority : Bool
    candidateHasMergeAuthorityIsFalse : candidateHasMergeAuthority ≡ false

open OntologyMergeCandidate public

-- Geometry convergence by itself remains explicitly non-promoting.  This
-- prevents a sparse or context-masked pair of classes from being merged just
-- because its current embedding is intermingled.
record GeometryOnlyMergeSignal : Set where
  constructor geometryOnlyMergeSignal
  field
    candidate : OntologyMergeCandidate
    residualBoundaryUnsupportedReference : String
    positiveConnectivityReference : String
    negativeConnectivityAbsentReference : String
    conditionalVariablesAccountedFor : Bool
    conditionalVariablesAccountedForIsTrue :
      conditionalVariablesAccountedFor ≡ true
    mergeReviewableFromGeometryAlone : Bool
    mergeReviewableFromGeometryAloneIsFalse :
      mergeReviewableFromGeometryAlone ≡ false

open GeometryOnlyMergeSignal public

-- A bounded impact report is required even after the semantic checks pass: a
-- class merge changes surrounding statements and projections, not merely two
-- labels.
record MergeImpactReport : Set where
  constructor mergeImpactReport
  field
    candidate : OntologyMergeCandidate
    affectedInstanceReference : String
    affectedSubclassEdgeReference : String
    affectedPropertyConstraintReference : String
    affectedDisjointnessReference : String
    affectedExternalIdentifierReference : String
    affectedQueryAndProjectionReference : String
    labelsAndAliasesToPreserveReference : String
    statementsRequiringReconstructionReference : String
    boundedImpact : Bool
    boundedImpactIsTrue : boundedImpact ≡ true
    provenanceTransferComplete : Bool
    provenanceTransferCompleteIsTrue : provenanceTransferComplete ≡ true
    automaticStatementRewrite : Bool
    automaticStatementRewriteIsFalse : automaticStatementRewrite ≡ false

open MergeImpactReport public

-- The conservative gate applies only to a direct merge.  Conditional
-- distinctions and bridge/new-superclass outcomes use their own dispositions
-- rather than being forced through this gate.
record ConservativeMergeGate : Set where
  constructor conservativeMergeGate
  field
    candidate : OntologyMergeCandidate
    impact : MergeImpactReport
    adequateCoverage : Bool
    adequateCoverageIsTrue : adequateCoverage ≡ true
    normativeCompatibilityPassed : Bool
    normativeCompatibilityPassedIsTrue : normativeCompatibilityPassed ≡ true
    noTypedIncompatibility : Bool
    noTypedIncompatibilityIsTrue : noTypedIncompatibility ≡ true
    noMeaningfulConditionalDistinction : Bool
    noMeaningfulConditionalDistinctionIsTrue :
      noMeaningfulConditionalDistinction ≡ true
    relationSubstitutabilityPassed : Bool
    relationSubstitutabilityPassedIsTrue : relationSubstitutabilityPassed ≡ true
    downstreamImpactBounded : Bool
    downstreamImpactBoundedIsTrue : downstreamImpactBounded ≡ true
    provenanceTransferComplete : Bool
    provenanceTransferCompleteIsTrue : provenanceTransferComplete ≡ true

open ConservativeMergeGate public

record CheckedMergeReviewReceipt : Set where
  constructor checkedMergeReviewReceipt
  field
    gate : ConservativeMergeGate
    disposition : MergeDisposition
    dispositionIsCheckedMergeReviewable :
      disposition ≡ checkedMergeReviewable
    reviewerAuthorityReference : String
    mergeApplied : Bool
    mergeAppliedIsFalse : mergeApplied ≡ false
    automaticClassRedirect : Bool
    automaticClassRedirectIsFalse : automaticClassRedirect ≡ false
    automaticOntologyMutation : Bool
    automaticOntologyMutationIsFalse : automaticOntologyMutation ≡ false

open CheckedMergeReviewReceipt public

checkedMergeStillDoesNotApplyMerge :
  (receipt : CheckedMergeReviewReceipt) →
  mergeApplied receipt ≡ false
checkedMergeStillDoesNotApplyMerge receipt =
  mergeAppliedIsFalse receipt

checkedMergeStillDoesNotRedirectClasses :
  (receipt : CheckedMergeReviewReceipt) →
  automaticClassRedirect receipt ≡ false
checkedMergeStillDoesNotRedirectClasses receipt =
  automaticClassRedirectIsFalse receipt

-- A failed or incomplete gate cannot be silently re-labelled as a successful
-- merge.  These dispositions preserve the alternative geometry for review.
mergeModeForBlockedEvidence :
  MergeDisposition →
  MergeMode
mergeModeForBlockedEvidence checkedMergeReviewable = exactDuplicateMerge
mergeModeForBlockedEvidence bridgeClassReviewPreferred = bridgeClassPreferred
mergeModeForBlockedEvidence sharedSuperclassReviewPreferred = sharedSuperclassOnly
mergeModeForBlockedEvidence conditionalDistinctionReviewPreserved =
  conditionalDistinctionPreserved
mergeModeForBlockedEvidence heldForMergeEvidence = mergeBlocked
mergeModeForBlockedEvidence contradictoryMergeCandidate = mergeBlocked
mergeModeForBlockedEvidence insufficientMergeCoverage = mergeInsufficientCoverage

insufficientCoveragePreservesMergeAbstention :
  mergeModeForBlockedEvidence insufficientMergeCoverage
  ≡
  mergeInsufficientCoverage
insufficientCoveragePreservesMergeAbstention = refl

contradictoryEvidenceBlocksMerge :
  mergeModeForBlockedEvidence contradictoryMergeCandidate ≡ mergeBlocked
contradictoryEvidenceBlocksMerge = refl

------------------------------------------------------------------------
-- Compact safety claim for the operational ABI.

governedResidualOntologyLearningStatement : String
governedResidualOntologyLearningStatement =
  "Policy anchors a domain invariant; independently reviewed conforming members may refine its empirical and conditional surfaces, while held, unresolved, and incomplete cases do not train it. Context-gated residual graphs may propose nearby classes, splits, disjointness, bridge superclasses, new abstractions, or class merges. Geometry convergence alone is not a merge: a direct merge needs normative compatibility, no typed or conditional obstruction, relation substitutability, bounded downstream impact, and complete provenance transfer. No spectral solve assigns truth, classes, redirects, or ontology edits automatically."
