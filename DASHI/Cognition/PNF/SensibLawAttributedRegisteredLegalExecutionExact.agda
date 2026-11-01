module DASHI.Cognition.PNF.SensibLawAttributedRegisteredLegalExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawAttributedAtomicCaseRegistryExact as AttributedRegistry
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as Implication
import DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact as RegisteredImplication
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawSourceConditionedTypedLiabilityExact as Typed
import DASHI.Cognition.PNF.SensibLawRegisteredTypedLiabilityExact as RegisteredLiability

------------------------------------------------------------------------
-- ATTRIBUTED REGISTERED LEGAL EXECUTION
--
-- Same-case coherence and source-conditioned execution are not enough for ITIR
-- reporting unless provenance remains recoverable at the execution boundary.
-- These wrappers bind the exact AttributedAtomicCaseRegistry to the exact
-- Registered... execution object. They create no new gate, authority, proof,
-- applicability, violation, liability, or promotion.
------------------------------------------------------------------------

record AttributedRegisteredAtomicLegalImplication
    {graph : Algebra.LegalGraph}
    {facts : Algebra.FactSet}
    {Enabled : Algebra.LegalRule → Set}
    {r : Algebra.LegalRule}
    {registry : Coherence.AtomicCaseRegistry}
    {caseContext : Ontology.StableId}
    {input : Implication.SourceConditionedAtomicLegalImplication graph facts Enabled r}
    (attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry)
    (registered :
      RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
        registry caseContext input) : Set₁ where
  constructor attributed-registered-atomic-legal-implication
  field
    executionAttributionReference : String

open AttributedRegisteredAtomicLegalImplication public

premiseDefinitionLineage :
  ∀ {graph facts Enabled r registry caseContext input}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
      registry caseContext input} →
  AttributedRegisteredAtomicLegalImplication attributedRegistry registered →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.premises r) →
  Provenance.ClaimLineageReceipt p
premiseDefinitionLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ membership =
  AttributedRegistry.definitionLineageFor attributedRegistry
    (RegisteredImplication.premiseEntry registered membership)

premiseOutcomeLineage :
  ∀ {graph facts Enabled r registry caseContext input}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
      registry caseContext input} →
  AttributedRegisteredAtomicLegalImplication attributedRegistry registered →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.premises r) →
  AttributedRegistry.AtomicEntryOutcomeLineage registry
    (RegisteredImplication.premiseEntry registered membership)
premiseOutcomeLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ membership =
  AttributedRegistry.outcomeLineageFor attributedRegistry
    (RegisteredImplication.premiseEntry registered membership)

premiseEvaluationLineage :
  ∀ {graph facts Enabled r registry caseContext input}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
      registry caseContext input} →
  AttributedRegisteredAtomicLegalImplication attributedRegistry registered →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.premises r) →
  AttributedRegistry.AtomicEvaluationLineageReceipt registry
    (RegisteredImplication.premiseEntry registered membership)
premiseEvaluationLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ membership =
  AttributedRegistry.evaluationLineageFor attributedRegistry
    (RegisteredImplication.premiseEntry registered membership)

record AttributedRegisteredTypedLiabilityDecision
    {state : Status.SemanticCommitmentState}
    {wrong : Ontology.WrongType}
    {bundle : Elements.WrongTypeRuleBundle wrong}
    {facts : Algebra.FactSet}
    {liabilityGraph : Algebra.LegalGraph}
    {profile : Downstream.TypedLiabilityProfile wrong}
    {realised : Typed.SourceConditionedTypedLiabilityProfile profile}
    {registry : Coherence.AtomicCaseRegistry}
    {caseContext : Ontology.StableId}
    {base : Typed.SourceConditionedTypedLiabilityDecision
      {state} {wrong} {bundle} {facts} liabilityGraph profile realised}
    (attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry)
    (registered : RegisteredLiability.RegisteredSourceConditionedTypedLiabilityDecision
      registry caseContext base) : Set₁ where
  constructor attributed-registered-typed-liability-decision
  field
    decisionAttributionReference : String

open AttributedRegisteredTypedLiabilityDecision public

familyDefinitionLineage :
  ∀ {state wrong bundle facts liabilityGraph profile realised registry caseContext base}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredLiability.RegisteredSourceConditionedTypedLiabilityDecision
      registry caseContext base} →
  AttributedRegisteredTypedLiabilityDecision attributedRegistry registered →
  Provenance.ClaimLineageReceipt (Typed.familyRecognitionProposition realised)
familyDefinitionLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ =
  AttributedRegistry.definitionLineageFor attributedRegistry
    (RegisteredLiability.familyEntry registered)

familyOutcomeLineage :
  ∀ {state wrong bundle facts liabilityGraph profile realised registry caseContext base}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredLiability.RegisteredSourceConditionedTypedLiabilityDecision
      registry caseContext base} →
  AttributedRegisteredTypedLiabilityDecision attributedRegistry registered →
  AttributedRegistry.AtomicEntryOutcomeLineage registry
    (RegisteredLiability.familyEntry registered)
familyOutcomeLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ =
  AttributedRegistry.outcomeLineageFor attributedRegistry
    (RegisteredLiability.familyEntry registered)

familyEvaluationLineage :
  ∀ {state wrong bundle facts liabilityGraph profile realised registry caseContext base}
    {attributedRegistry : AttributedRegistry.AttributedAtomicCaseRegistry registry}
    {registered : RegisteredLiability.RegisteredSourceConditionedTypedLiabilityDecision
      registry caseContext base} →
  AttributedRegisteredTypedLiabilityDecision attributedRegistry registered →
  AttributedRegistry.AtomicEvaluationLineageReceipt registry
    (RegisteredLiability.familyEntry registered)
familyEvaluationLineage {attributedRegistry = attributedRegistry}
  {registered = registered} _ =
  AttributedRegistry.evaluationLineageFor attributedRegistry
    (RegisteredLiability.familyEntry registered)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AttributionWrapperCreatesExecution : Set where
data AttributionWrapperCreatesAuthority : Set where
data AttributionWrapperCreatesPromotion : Set where
data RegisteredExecutionMayDiscardProvenance : Set where
data RepositoryEvaluationMayBeReportedAsCourtAuthoredGate : Set where

attributionWrapperDoesNotCreateExecution : AttributionWrapperCreatesExecution → ⊥
attributionWrapperDoesNotCreateExecution ()

attributionWrapperDoesNotCreateAuthority : AttributionWrapperCreatesAuthority → ⊥
attributionWrapperDoesNotCreateAuthority ()

attributionWrapperDoesNotCreatePromotion : AttributionWrapperCreatesPromotion → ⊥
attributionWrapperDoesNotCreatePromotion ()

registeredExecutionCannotDiscardProvenanceByPermission :
  RegisteredExecutionMayDiscardProvenance → ⊥
registeredExecutionCannotDiscardProvenanceByPermission ()

repositoryGateCannotBeReportedAsCourtAuthoredByPermission :
  RepositoryEvaluationMayBeReportedAsCourtAuthoredGate → ⊥
repositoryGateCannotBeReportedAsCourtAuthoredByPermission ()

record AttributedRegisteredLegalExecutionBoundary : Set where
  constructor attributed-registered-legal-execution-boundary
  field
    registeredExecutionRetained : Bool
    attributedRegistryRetained : Bool
    premiseLineageRecoverable : Bool
    liabilityFamilyLineageRecoverable : Bool
    attributionCreatesExecution : Bool
    attributionCreatesPromotion : Bool

canonicalAttributedRegisteredLegalExecutionBoundary :
  AttributedRegisteredLegalExecutionBoundary
canonicalAttributedRegisteredLegalExecutionBoundary =
  attributed-registered-legal-execution-boundary true true true true false false
