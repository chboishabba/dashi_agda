module DASHI.Reasoning.Spacy369CriticalAuditDiscriminatorPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer
import DASHI.Reasoning.Spacy369CriticalRelationalAuditExact as Audit
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace

------------------------------------------------------------------------
-- CONSUMER-RELATIVE EXPERIMENT/DISCRIMINATOR PLANNING ON THE MATERIALISED
-- SENSIBLAW SPACY / PNF / 369 FIXTURE.
--
-- The operational consumer is already constant on the live broad/narrow fibre,
-- so the correct sequential plan is terminal: ask nothing.
--
-- Scope and subject-position consumers remain nonconstant.  Each receives a
-- distinct one-shot discriminator that reads exactly the coordinate required by
-- that consumer.  The bundles are finite DASHI information-design fixtures;
-- they are not claims that a philosophical audit itself performs a laboratory
-- measurement or that the parser already observed the missing coordinate.
------------------------------------------------------------------------

data ScopeEvidence : Set where
  initialScopeEvidence : ScopeEvidence

scopeCompatible :
  Envelope.Compatible ScopeEvidence Candidate.CandidateSemanticFragment
scopeCompatible initialScopeEvidence =
  Semantic.semanticCandidateFibre Trace.candidateFibre

scopeBundle : Discriminator.ExperimentBundle Candidate.CandidateSemanticFragment
scopeBundle =
  Discriminator.experimentBundle
    Consumer.ScopeDecision
    Consumer.scopeConsumer
    1
    "materialised-spacy: review negation/coordination scope"
    "scope outcome must be source/context reviewed; spaCy dependency shape alone does not settle scope"

scopeBundleClosesScopeConsumer :
  Discriminator.ProspectivelyClosesConsumer
    scopeCompatible Consumer.scopeConsumer scopeBundle
scopeBundleClosesScopeConsumer evidence witness witnessCompatible
    left right leftCompatible rightCompatible =
  trans (proj₂ leftCompatible) (sym (proj₂ rightCompatible))

scopeSequentialPlan :
  Sequential.SequentialConsumerPlan
    Consumer.scopeConsumer
    (scopeCompatible initialScopeEvidence)
scopeSequentialPlan =
  Sequential.oneShotConsumerClosingPlan
    scopeCompatible
    Consumer.scopeConsumer
    initialScopeEvidence
    scopeBundle
    scopeBundleClosesScopeConsumer

------------------------------------------------------------------------
-- Already-closed operational consumer: no experiment is required.
------------------------------------------------------------------------

operationalSequentialPlan :
  Sequential.SequentialConsumerPlan
    Consumer.operationalConsumer
    (scopeCompatible initialScopeEvidence)
operationalSequentialPlan =
  Sequential.closeConsumer Consumer.operationalConsumerClosedOnMaterialisedFibre

------------------------------------------------------------------------
-- Subject-position information lives on a finer situated carrier.  The
-- parser/369 surface deliberately collides on represented/originating states.
------------------------------------------------------------------------

data SubjectEvidence : Set where
  initialSubjectEvidence : SubjectEvidence

subjectCompatible :
  Envelope.Compatible SubjectEvidence Consumer.SituatedSpacyReading
subjectCompatible initialSubjectEvidence state = ⊤

subjectConsumer : Consumer.SituatedSpacyReading → Subject.SubjectPosition
subjectConsumer = Consumer.subjectPositionResidual

subjectPositionBundle :
  Discriminator.ExperimentBundle Consumer.SituatedSpacyReading
subjectPositionBundle =
  Discriminator.experimentBundle
    Subject.SubjectPosition
    Consumer.subjectPositionResidual
    2
    "critical-audit: acquire originating/represented subject-position evidence"
    "subject-position coordinate requires independent provenance/situated evidence; it is not reconstructed from parser or 369 output"

subjectBundleClosesSubjectConsumer :
  Discriminator.ProspectivelyClosesConsumer
    subjectCompatible subjectConsumer subjectPositionBundle
subjectBundleClosesSubjectConsumer evidence witness witnessCompatible
    left right leftCompatible rightCompatible =
  trans (proj₂ leftCompatible) (sym (proj₂ rightCompatible))

subjectSequentialPlan :
  Sequential.SequentialConsumerPlan
    subjectConsumer
    (subjectCompatible initialSubjectEvidence)
subjectSequentialPlan =
  Sequential.oneShotConsumerClosingPlan
    subjectCompatible
    subjectConsumer
    initialSubjectEvidence
    subjectPositionBundle
    subjectBundleClosesSubjectConsumer

subjectBundleSeparatesParserCollision :
  Discriminator.BundleSeparates
    subjectPositionBundle
    Consumer.representedReading
    Consumer.originatingReading
subjectBundleSeparatesParserCollision =
  Discriminator.bundleSeparates Consumer.subjectPositionsDiffer

subjectPositionExtendsParserLanguage :
  Discriminator.DiscriminatingLanguageExtension Consumer.parserSemanticSurface
subjectPositionExtendsParserLanguage =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      Consumer.representedReading
      Consumer.originatingReading
      refl)
    subjectPositionBundle
    subjectBundleSeparatesParserCollision

------------------------------------------------------------------------
-- Audit lens -> information policy.  Closure/context/reciprocity/intersection
-- audits remain typed demands here; this owner does not invent observations
-- that the materialised corpus does not contain.
------------------------------------------------------------------------

data AuditInformationPolicy : Set where
  noFurtherProbe
  runScopeDiscriminator
  acquireSubjectPositionCoordinate
  inspectClosureResidual
  inspectReciprocalRelation
  acquireSituatedIntersectionalCoordinate
  : AuditInformationPolicy

policyForAudit : Audit.CriticalAuditLens → AuditInformationPolicy
policyForAudit Audit.parserScopeAudit = runScopeDiscriminator
policyForAudit Audit.lacanianClosureResidualAudit = inspectClosureResidual
policyForAudit Audit.feministSubjectPositionAudit = acquireSubjectPositionCoordinate
policyForAudit Audit.irigarayanReciprocalRelationAudit = inspectReciprocalRelation
policyForAudit Audit.intersectionalMissingCoordinateAudit =
  acquireSituatedIntersectionalCoordinate

operationalConsumerPolicy : AuditInformationPolicy
operationalConsumerPolicy = noFurtherProbe

scopePolicyDistinctFromSubjectPolicy :
  policyForAudit Audit.parserScopeAudit
  ≡ policyForAudit Audit.feministSubjectPositionAudit → ⊥
scopePolicyDistinctFromSubjectPolicy ()

closurePolicyDistinctFromReciprocalPolicy :
  policyForAudit Audit.lacanianClosureResidualAudit
  ≡ policyForAudit Audit.irigarayanReciprocalRelationAudit → ⊥
closurePolicyDistinctFromReciprocalPolicy ()

record Spacy369CriticalAuditDiscriminatorBoundary : Set where
  constructor spacy369CriticalAuditDiscriminatorBoundary
  field
    closedOperationalConsumerShouldAskAnotherQuestion : Bool
    closedOperationalConsumerShouldAskAnotherQuestionIsFalse :
      closedOperationalConsumerShouldAskAnotherQuestion ≡ false
    scopeConsumerCanUseDedicatedConsumerClosingProbe : Bool
    scopeConsumerCanUseDedicatedConsumerClosingProbeIsTrue :
      scopeConsumerCanUseDedicatedConsumerClosingProbe ≡ true
    subjectPositionNeedsAddedObservationCoordinate : Bool
    subjectPositionNeedsAddedObservationCoordinateIsTrue :
      subjectPositionNeedsAddedObservationCoordinate ≡ true
    subjectCoordinateIsRecoveredByRelabelling369 : Bool
    subjectCoordinateIsRecoveredByRelabelling369IsFalse :
      subjectCoordinateIsRecoveredByRelabelling369 ≡ false
    everyCriticalAuditIsTheSameMeasurement : Bool
    everyCriticalAuditIsTheSameMeasurementIsFalse :
      everyCriticalAuditIsTheSameMeasurement ≡ false
    oneProbeMustIdentifyTheWholeSemanticWorld : Bool
    oneProbeMustIdentifyTheWholeSemanticWorldIsFalse :
      oneProbeMustIdentifyTheWholeSemanticWorld ≡ false
    philosophicalAuditItselfManufacturesMissingEvidence : Bool
    philosophicalAuditItselfManufacturesMissingEvidenceIsFalse :
      philosophicalAuditItselfManufacturesMissingEvidence ≡ false

canonicalSpacy369CriticalAuditDiscriminatorBoundary :
  Spacy369CriticalAuditDiscriminatorBoundary
canonicalSpacy369CriticalAuditDiscriminatorBoundary =
  spacy369CriticalAuditDiscriminatorBoundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
