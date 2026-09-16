module DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Provenance
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDStructuredSearchExact as Search

------------------------------------------------------------------------
-- DIGITAL-ESD MANUSCRIPT DEPENDENCY / PAYMENT ADAPTER
--
-- Thin application instance only. Graph semantics come from
-- TypedProvenanceDependencyGraphExact; structured-search execution genealogy
-- comes from DigitalESDStructuredSearchExact; payment/frontier feedback comes
-- from the canonical SensibLaw assessment/feedback owners already reused
-- cross-domain in the repository.
--
-- Acquisition may happen out of dependency order. Final manuscript payment may
-- not skip a required edge. Source counts, citations, graph membership and
-- scheduler transitions create neither truth nor authority.
------------------------------------------------------------------------

structuredSearchExecutionNode : Provenance.DependencyNode
structuredSearchExecutionNode =
  Provenance.dependencyNode
    "transparent structured-search execution closure"
    Provenance.runtimeAcquisition
    "exact database-export -> deduplication -> screening -> extraction lineage; currently unobserved as a closed receipt"
    false

eligibleCorpusNode : Provenance.DependencyNode
eligibleCorpusNode =
  Provenance.dependencyNode
    "eligible extracted digital-ESD corpus"
    Provenance.dashiFormal
    "consumer-scoped corpus produced from the retained structured-search lineage; not identical to every acquired snowball source"
    false

sourceScopeMatrixNode : Provenance.DependencyNode
sourceScopeMatrixNode =
  Provenance.dependencyNode
    "source-role and scope synthesis matrix"
    Provenance.dashiFormal
    "matrix retaining source identity, role, consumer scope, same-object status and non-promotion boundaries"
    false

lifecycleSynthesisNode : Provenance.DependencyNode
lifecycleSynthesisNode =
  Provenance.dependencyNode
    "lifecycle / circularity evidence synthesis"
    Provenance.dashiFormal
    "manuscript synthesis over eligible source-scoped lifecycle evidence; does not manufacture deployment-specific LCI"
    false

participantGovernanceSynthesisNode : Provenance.DependencyNode
participantGovernanceSynthesisNode =
  Provenance.dependencyNode
    "participant-governance evidence synthesis"
    Provenance.dashiFormal
    "manuscript synthesis over eligible source-scoped participation evidence; does not create local participant authority"
    false

longitudinalSynthesisNode : Provenance.DependencyNode
longitudinalSynthesisNode =
  Provenance.dependencyNode
    "longitudinal / institutional-impact evidence synthesis"
    Provenance.dashiFormal
    "manuscript synthesis over eligible source-scoped longitudinal evidence; does not observe future intervention outcomes"
    false

------------------------------------------------------------------------
-- Required manuscript-payment edges.
--
-- These are payment dependencies, not acquisition-order constraints. A paper
-- may already have acquired relevant lifecycle or participant literature, but
-- final synthesis closure cannot pretend that an unclosed search/corpus/scope
-- dependency was paid merely because a downstream source arrived earlier.
------------------------------------------------------------------------

searchToEligibleCorpus : Provenance.DependencyEdge
searchToEligibleCorpus =
  Provenance.dependencyEdge
    structuredSearchExecutionNode
    eligibleCorpusNode
    Provenance.acquisitionRole
    true
    "eligible-corpus payment requires the exact structured-search execution lineage; open-web snowball acquisition alone cannot substitute for this required support"

eligibleCorpusToSourceScope : Provenance.DependencyEdge
eligibleCorpusToSourceScope =
  Provenance.dependencyEdge
    eligibleCorpusNode
    sourceScopeMatrixNode
    Provenance.evidenceRole
    true
    "source/scope synthesis is paid only against the eligible retained corpus rather than an unscoped bibliography"

sourceScopeToLifecycleSynthesis : Provenance.DependencyEdge
sourceScopeToLifecycleSynthesis =
  Provenance.dependencyEdge
    sourceScopeMatrixNode
    lifecycleSynthesisNode
    Provenance.evidenceRole
    true
    "lifecycle synthesis must retain source role/scope before contextual method evidence is interpreted; deployment-specific evidence remains separately unpaid"

sourceScopeToParticipantGovernanceSynthesis : Provenance.DependencyEdge
sourceScopeToParticipantGovernanceSynthesis =
  Provenance.dependencyEdge
    sourceScopeMatrixNode
    participantGovernanceSynthesisNode
    Provenance.authorityBoundaryRole
    true
    "participant-governance synthesis must retain scope and authority boundaries; prior participation literature cannot create local constitutive authority"

sourceScopeToLongitudinalSynthesis : Provenance.DependencyEdge
sourceScopeToLongitudinalSynthesis =
  Provenance.dependencyEdge
    sourceScopeMatrixNode
    longitudinalSynthesisNode
    Provenance.evidenceRole
    true
    "longitudinal synthesis must retain study/population/time scope; prior follow-up studies cannot observe the future outcome of a different intervention"

canonicalManuscriptDependencyGraph : Provenance.TypedDependencyGraph
canonicalManuscriptDependencyGraph =
  Provenance.typedDependencyGraph
    "digital-ESD integrative-review manuscript payment dependencies"
    ( structuredSearchExecutionNode
    ∷ eligibleCorpusNode
    ∷ sourceScopeMatrixNode
    ∷ lifecycleSynthesisNode
    ∷ participantGovernanceSynthesisNode
    ∷ longitudinalSynthesisNode
    ∷ [] )
    ( searchToEligibleCorpus
    ∷ eligibleCorpusToSourceScope
    ∷ sourceScopeToLifecycleSynthesis
    ∷ sourceScopeToParticipantGovernanceSynthesis
    ∷ sourceScopeToLongitudinalSynthesis
    ∷ [] )

canonicalManuscriptProvenanceBoundary :
  Provenance.TypedProvenanceDependencyBoundary
canonicalManuscriptProvenanceBoundary =
  Provenance.canonicalTypedProvenanceDependencyBoundary

manuscriptProvenanceLoad : Provenance.ProvenanceLoadSummary
manuscriptProvenanceLoad =
  Provenance.summarizeProvenanceLoad canonicalManuscriptDependencyGraph

------------------------------------------------------------------------
-- Executable payment seam.
--
-- Search closure itself does not pay the downstream syntheses. It is required
-- support for the eligible corpus. The source/scope matrix then carries the
-- exact search closure as an upstream object, giving downstream consumers a
-- structural genealogy rather than a copied Boolean status.
------------------------------------------------------------------------

record SourceScopeMatrixPayment
    (searchClosure : Search.TransparentStructuredSearchClosureReceipt) : Set where
  constructor source-scope-matrix-payment
  field
    sourceScopeMatrixReference : String
    eligibleCorpusReference : String
    searchExecutionLineageRetained : Bool
    searchExecutionLineageRetainedIsTrue :
      searchExecutionLineageRetained ≡ true
    citationCreatesProof : Bool
    citationCreatesProofIsFalse : citationCreatesProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open SourceScopeMatrixPayment public

record ManuscriptEvidenceSynthesisAdmission : Set where
  constructor manuscript-evidence-synthesis-admission
  field
    searchClosure : Search.TransparentStructuredSearchClosureReceipt
    sourceScopePayment : SourceScopeMatrixPayment searchClosure
    lifecycleSynthesisReference : String
    participantGovernanceSynthesisReference : String
    longitudinalSynthesisReference : String
    requiredDependencyLineageRetained : Bool
    requiredDependencyLineageRetainedIsTrue :
      requiredDependencyLineageRetained ≡ true
    createsEmpiricalSameObjectEvidence : Bool
    createsEmpiricalSameObjectEvidenceIsFalse :
      createsEmpiricalSameObjectEvidence ≡ false
    createsParticipantAuthority : Bool
    createsParticipantAuthorityIsFalse : createsParticipantAuthority ≡ false

open ManuscriptEvidenceSynthesisAdmission public

------------------------------------------------------------------------
-- Mabo-pattern payment firewall: a required support coordinate cannot be
-- replaced by an explicit residual merely to make the downstream object look
-- complete. Residuals may remain visible; they cannot pay required support.
------------------------------------------------------------------------

data RequiredStructuredSearchSupportMayBeResidualized : Set where

requiredStructuredSearchSupportCannotBeResidualized :
  RequiredStructuredSearchSupportMayBeResidualized → ⊥
requiredStructuredSearchSupportCannotBeResidualized ()

data EarlyDownstreamAcquisitionPaysSkippedDependency : Set where

earlyAcquisitionDoesNotPaySkippedDependency :
  EarlyDownstreamAcquisitionPaysSkippedDependency → ⊥
earlyAcquisitionDoesNotPaySkippedDependency ()

data DependencyGraphCreatesTruthOrAuthority : Set where

dependencyGraphDoesNotCreateTruthOrAuthority :
  DependencyGraphCreatesTruthOrAuthority → ⊥
dependencyGraphDoesNotCreateTruthOrAuthority ()

------------------------------------------------------------------------
-- Pareto/frontier feedback reuse.
--
-- We do not invent another state machine. The canonical feedback owner already
-- says an admitted narrowing or contested reopening recomputes the live
-- frontier, while its boundary retains old source history and requires stale
-- cuts/frontiers to be recomputed.
------------------------------------------------------------------------

admittedSearchNarrowingRerunsPareto :
  Feedback.feedbackDisposition
    Assessment.proofPaymentAdmitted
    Assessment.frontierNarrowed
  ≡ Feedback.recomputeFrontier
admittedSearchNarrowingRerunsPareto =
  Feedback.admittedNarrowingRecomputes

reopenedSearchFrontierRerunsPareto :
  Feedback.feedbackDisposition
    Assessment.proofPaymentContested
    Assessment.frontierReopened
  ≡ Feedback.recomputeFrontier
reopenedSearchFrontierRerunsPareto = refl

canonicalFeedbackBoundaryRetained :
  Feedback.AdaptiveLegalResearchFeedbackBoundary
canonicalFeedbackBoundaryRetained =
  Feedback.canonicalAdaptiveLegalResearchFeedbackBoundary

canonicalAssessmentBoundaryRetained : Assessment.ResultAssessmentBoundary
canonicalAssessmentBoundaryRetained = Assessment.canonicalResultAssessmentBoundary

------------------------------------------------------------------------
-- Current paper status stays honest.
------------------------------------------------------------------------

currentPaperRequiresStructuredSearch :
  Paper.requiredFor
    Paper.integrativeConceptualReview
    Paper.transparentStructuredSearch
  ≡ true
currentPaperRequiresStructuredSearch = refl

currentStructuredSearchStillOpen :
  Paper.closed Paper.transparentStructuredSearch ≡ false
currentStructuredSearchStillOpen = refl

searchClosureDoesNotPayEvidenceSynthesis :
  Search.StructuredSearchClosurePaysEvidenceSynthesis → ⊥
searchClosureDoesNotPayEvidenceSynthesis =
  Search.structuredSearchClosureDoesNotPayEvidenceSynthesis

record ManuscriptDependencyPaymentBoundary : Set where
  constructor manuscript-dependency-payment-boundary
  field
    canonicalTypedProvenanceGraphReused : Bool
    canonicalTypedProvenanceGraphReusedIsTrue :
      canonicalTypedProvenanceGraphReused ≡ true
    acquisitionMayOccurOutOfDependencyOrder : Bool
    acquisitionMayOccurOutOfDependencyOrderIsTrue :
      acquisitionMayOccurOutOfDependencyOrder ≡ true
    downstreamPaymentMaySkipRequiredDependency : Bool
    downstreamPaymentMaySkipRequiredDependencyIsFalse :
      downstreamPaymentMaySkipRequiredDependency ≡ false
    requiredSupportMayBeResidualizedAway : Bool
    requiredSupportMayBeResidualizedAwayIsFalse :
      requiredSupportMayBeResidualizedAway ≡ false
    paymentOrReopeningRecomputesParetoFrontier : Bool
    paymentOrReopeningRecomputesParetoFrontierIsTrue :
      paymentOrReopeningRecomputesParetoFrontier ≡ true
    oldEvidenceHistoryPreservedAcrossRerun : Bool
    oldEvidenceHistoryPreservedAcrossRerunIsTrue :
      oldEvidenceHistoryPreservedAcrossRerun ≡ true
    dependencyGraphCreatesTruth : Bool
    dependencyGraphCreatesTruthIsFalse : dependencyGraphCreatesTruth ≡ false
    dependencyGraphCreatesAuthority : Bool
    dependencyGraphCreatesAuthorityIsFalse :
      dependencyGraphCreatesAuthority ≡ false

open ManuscriptDependencyPaymentBoundary public

canonicalManuscriptDependencyPaymentBoundary :
  ManuscriptDependencyPaymentBoundary
canonicalManuscriptDependencyPaymentBoundary =
  manuscript-dependency-payment-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

highestAlphaManuscriptDependencyReading : String
highestAlphaManuscriptDependencyReading =
  "The digital-ESD paper now instantiates the repository's canonical typed provenance dependency graph rather than defining a new workflow calculus. Acquisition remains snowball-permissive, but final manuscript payment cannot skip structured-search -> eligible-corpus -> source/scope dependencies. The current search coordinate remains open. When an assessed payment narrows or reopens the live frontier, the canonical feedback owner requires recomputation while preserving append-only evidence history."
