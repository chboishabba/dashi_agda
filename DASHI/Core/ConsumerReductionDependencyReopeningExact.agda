module DASHI.Core.ConsumerReductionDependencyReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Core.StructuredResidualProductExact as Residual

------------------------------------------------------------------------
-- PURPOSE
--
-- A calibration/source/model change should reopen exactly the reduction
-- certificates that depend on it, not silently invalidate the whole repo and
-- not leave downstream consumers stale.  This owner cross-pollinates the
-- existing reverse-dependency closure, reopenable-hypothesis and structured
-- residual surfaces with consumer-relative model reduction.
------------------------------------------------------------------------

data ReductionArtifact : Set where
  rawEvidenceArtifact
  geometryArtifact
  constitutiveModelArtifact
  calibrationArtifact
  reductionCertificateArtifact
  consumerDecisionArtifact
  interventionArtifact
  : ReductionArtifact

record ReductionDependencyGraph : Set₁ where
  constructor reductionDependencyGraph
  field
    Depends : ReductionArtifact → ReductionArtifact → Set
    dependencyReference : String

open ReductionDependencyGraph public

record ReductionChange : Set where
  constructor reductionChange
  field
    changedArtifact : ReductionArtifact
    changeReference : String

open ReductionChange public

record SelectiveReductionReopening
    (graph : ReductionDependencyGraph)
    (change : ReductionChange) : Set₁ where
  constructor selectiveReductionReopening
  field
    target : ReductionArtifact
    obligation :
      Dependency.ReopeningObligation
        (Depends graph)
        (changedArtifact change)
        target
    reopeningReference : String

open SelectiveReductionReopening public

certificateReopensWhenCalibrationDependencyPathExists :
  ∀ {graph : ReductionDependencyGraph} →
  Dependency.AffectedClosure
    (Depends graph)
    calibrationArtifact
    reductionCertificateArtifact →
  SelectiveReductionReopening
    graph
    (reductionChange calibrationArtifact "calibration changed")
certificateReopensWhenCalibrationDependencyPathExists path =
  selectiveReductionReopening
    reductionCertificateArtifact
    (Dependency.reopeningObligation path)
    "recheck consumer-relative reduction certificate"

consumerDecisionReopensTransitively :
  ∀ {graph : ReductionDependencyGraph}
    {change : ReductionChange} →
  SelectiveReductionReopening graph change →
  Dependency.ReopeningObligation
    (Depends graph)
    reductionCertificateArtifact
    consumerDecisionArtifact →
  Dependency.ReopeningObligation
    (Depends graph)
    (changedArtifact change)
    consumerDecisionArtifact
consumerDecisionReopensTransitively reopening downstream =
  Dependency.obligationsCompose
    (obligation reopening)
    downstream

------------------------------------------------------------------------
-- Structured residual plan.  A model/calibration change is initially a model
-- fidelity reopening, not fabricated new raw evidence or an authority change.
------------------------------------------------------------------------

modelChangeResidualPlan : Residual.StructuredReopeningPlan
modelChangeResidualPlan = Residual.onlyModelFidelityAffected

modelChangeDoesNotInventRawEvidenceChange :
  Residual.affected
    (Residual.rawEvidenceReopening modelChangeResidualPlan)
  ≡ false
modelChangeDoesNotInventRawEvidenceChange =
  Residual.modelOnlyDoesNotMarkRawEvidenceAffected

------------------------------------------------------------------------
-- Candidate status transition: stale certification is reopenable, not refuted.
-- Refutation still requires the candidate's actual future-separating witness.
------------------------------------------------------------------------

reopenCandidateForChangedDependency :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    (candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe) →
  Forest.HypothesisTransition
    Search.reductionHypothesisSemantics
    candidate
    Forest.active
    (Forest.reopenable Forest.dependencyChanged)
reopenCandidateForChangedDependency candidate =
  Forest.defer Forest.dependencyChanged

staleCertificateDoesNotRefuteCandidate :
  ∀ {Fine Action Observation}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe} →
  Forest.HypothesisTransition
    Search.reductionHypothesisSemantics
    candidate
    (Forest.reopenable Forest.dependencyChanged)
    Forest.refuted →
  ⊥
staleCertificateDoesNotRefuteCandidate =
  Search.noDeferredCandidateAutoRefutation

record ReductionDependencyReopeningBoundary : Set where
  constructor reductionDependencyReopeningBoundary
  field
    calibrationChangeMayRequireCertificateRecheck : Bool
    calibrationChangeMayRequireCertificateRecheckIsTrue :
      calibrationChangeMayRequireCertificateRecheck ≡ true
    downstreamConsumerMayReopenTransitively : Bool
    downstreamConsumerMayReopenTransitivelyIsTrue :
      downstreamConsumerMayReopenTransitively ≡ true
    modelChangeAutomaticallyChangesRawEvidence : Bool
    modelChangeAutomaticallyChangesRawEvidenceIsFalse :
      modelChangeAutomaticallyChangesRawEvidence ≡ false
    staleCertificateEqualsCandidateRefutation : Bool
    staleCertificateEqualsCandidateRefutationIsFalse :
      staleCertificateEqualsCandidateRefutation ≡ false
    unrelatedArtifactsMustReopenWithoutDependencyPath : Bool
    unrelatedArtifactsMustReopenWithoutDependencyPathIsFalse :
      unrelatedArtifactsMustReopenWithoutDependencyPath ≡ false

canonicalReductionDependencyReopeningBoundary :
  ReductionDependencyReopeningBoundary
canonicalReductionDependencyReopeningBoundary =
  reductionDependencyReopeningBoundary
    true refl true refl false refl false refl false refl
