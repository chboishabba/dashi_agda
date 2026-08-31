module DASHI.Reasoning.SemanticEpistemicPathReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.SemanticEpistemicInterpretationExact as SemEpi
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path
import DASHI.Reasoning.DerivationEdgeInstanceSelectiveReopeningExact as EdgePath

------------------------------------------------------------------------
-- SYSTEM MEANING CERTIFICATES WITH EXACT DERIVATION-PATH DEPENDENCIES
--
-- A governance / political-economy interpretation is not just a label on an
-- observation.  Once it is evidence-qualified or supported, it should retain
-- the exact derivation path by which its evidential obligations were discharged.
-- A later change to one edge instance therefore reopens only meanings whose
-- own path actually contains that edge.
------------------------------------------------------------------------

record MeaningDerivationReceipt
    (problem : SemEpi.SemanticEpistemicProblem)
    (meaning : SemEpi.Meaning problem) : Set₁ where
  constructor meaningDerivationReceipt
  field
    certificate : EdgePath.IndexedConsequenceCertificate
    interpretationScale : SemEpi.InterpretationScale
    scaleMatchesMeaning :
      interpretationScale ≡ SemEpi.scale problem meaning
    meaningReference : String
    evidenceAuditReference : String
    semanticCorrespondenceReference : String

open MeaningDerivationReceipt public

record MeaningDependsOnEdge
    {problem : SemEpi.SemanticEpistemicProblem}
    {meaning : SemEpi.Meaning problem}
    (receipt : MeaningDerivationReceipt problem meaning)
    {edgeFrom edgeTo}
    (edge : EdgePath.IndexedDerivationEdge edgeFrom edgeTo) : Set where
  constructor meaningDependsOnEdge
  field
    occurrence :
      EdgePath.EdgeOccurs edge
        (EdgePath.derivation (certificate receipt))
    dependencyReference : String

open MeaningDependsOnEdge public

meaningEdgeChangeCreatesReopening :
  ∀ {problem meaning edgeFrom edgeTo}
    {receipt : MeaningDerivationReceipt problem meaning}
    {edge : EdgePath.IndexedDerivationEdge edgeFrom edgeTo} →
  MeaningDependsOnEdge receipt edge →
  Dependency.ReopeningObligation
    (EdgePath.OccurrenceDepends edge (certificate receipt))
    EdgePath.changedEdgeInstanceArtifact
    EdgePath.consequenceCertificateArtifact
meaningEdgeChangeCreatesReopening dependency =
  EdgePath.edgeOccurrenceCreatesReopeningObligation
    (occurrence dependency)

------------------------------------------------------------------------
-- Non-occurrence means this particular local edge instance cannot be used as
-- the dependency witness for reopening this meaning certificate.
------------------------------------------------------------------------

unrelatedEdgeCannotCreateDirectMeaningDependency :
  ∀ {problem meaning edgeFrom edgeTo}
    {receipt : MeaningDerivationReceipt problem meaning}
    {edge : EdgePath.IndexedDerivationEdge edgeFrom edgeTo} →
  EdgePath.DoesNotOccur edge
    (EdgePath.derivation (certificate receipt)) →
  EdgePath.OccurrenceDepends edge (certificate receipt)
    EdgePath.changedEdgeInstanceArtifact
    EdgePath.consequenceCertificateArtifact →
  ⊥
unrelatedEdgeCannotCreateDirectMeaningDependency =
  EdgePath.nonOccurrenceBlocksDirectDependency

------------------------------------------------------------------------
-- Reopening is epistemic staleness, not automatic falsification.  A revised
-- assay, recurrence estimate, enforcement record or incentive premise can make
-- one interpretation stale without proving its negation.
------------------------------------------------------------------------

data MeaningCertificateStatus : Set where
  currentMeaningCertificate
  reopenableMeaningCertificate
  refutedMeaningCertificate
  : MeaningCertificateStatus

reopenableMeaningNotRefuted :
  reopenableMeaningCertificate ≡ refutedMeaningCertificate → ⊥
reopenableMeaningNotRefuted ()

record MeaningReopeningReceipt
    {problem : SemEpi.SemanticEpistemicProblem}
    {meaning : SemEpi.Meaning problem}
    (receipt : MeaningDerivationReceipt problem meaning) : Set₁ where
  constructor meaningReopeningReceipt
  field
    edgeFrom edgeTo : Path.DerivationNode
    changedEdge : EdgePath.IndexedDerivationEdge edgeFrom edgeTo
    dependsOnChangedEdge : MeaningDependsOnEdge receipt changedEdge
    reopening :
      Dependency.ReopeningObligation
        (EdgePath.OccurrenceDepends changedEdge (certificate receipt))
        EdgePath.changedEdgeInstanceArtifact
        EdgePath.consequenceCertificateArtifact
    reopeningReference : String

open MeaningReopeningReceipt public

record SemanticEpistemicPathReopeningBoundary : Set where
  constructor semanticEpistemicPathReopeningBoundary
  field
    meaningSupportCanRetainExactDerivationPath : Bool
    meaningSupportCanRetainExactDerivationPathIsTrue :
      meaningSupportCanRetainExactDerivationPath ≡ true
    changedPremiseReopensMeaningOnlyWhenPathDependsOnIt : Bool
    changedPremiseReopensMeaningOnlyWhenPathDependsOnItIsTrue :
      changedPremiseReopensMeaningOnlyWhenPathDependsOnIt ≡ true
    sameInterpretationScaleForcesSameDependencies : Bool
    sameInterpretationScaleForcesSameDependenciesIsFalse :
      sameInterpretationScaleForcesSameDependencies ≡ false
    reopenedMeaningEqualsRefutedMeaning : Bool
    reopenedMeaningEqualsRefutedMeaningIsFalse :
      reopenedMeaningEqualsRefutedMeaning ≡ false

canonicalSemanticEpistemicPathReopeningBoundary :
  SemanticEpistemicPathReopeningBoundary
canonicalSemanticEpistemicPathReopeningBoundary =
  semanticEpistemicPathReopeningBoundary
    true refl
    true refl
    false refl
    false refl
