module DASHI.Cognition.PNF.SensibLawRegisteredApplicabilityViolationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact as RegisteredImplication
import DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact as SourceConditioned

------------------------------------------------------------------------
-- REGISTERED APPLICABILITY / VIOLATION
--
-- SourceConditionedApplicabilityViolationExact remains the canonical
-- source/rule/derivation owner.  This module adds the case-outcome coherence
-- required for executable case reasoning: every atomic implication used at
-- applicability and every WrongElement authority rule is bound to the same
-- finite AtomicCaseRegistry and case context.
------------------------------------------------------------------------

record RegisteredSourceConditionedApplicability
    {state : Status.SemanticCommitmentState}
    {graph : Algebra.LegalGraph}
    {facts : Algebra.FactSet}
    {Enabled : Algebra.LegalRule → Set}
    {r : Algebra.LegalRule}
    (registry : Coherence.AtomicCaseRegistry)
    (caseContext : Ontology.StableId)
    (base : SourceConditioned.SourceConditionedApplicability {state} graph facts Enabled r) : Set₁ where
  constructor registered-source-conditioned-applicability
  field
    registeredRuleApplication :
      RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
        registry
        caseContext
        (SourceConditioned.atomicRuleApplication base)
    registrationReference : String

open RegisteredSourceConditionedApplicability public

record RegisteredSourceConditionedElementRequirement
    {wrong : Ontology.WrongType}
    {bundle : Elements.WrongTypeRuleBundle wrong}
    {facts : Algebra.FactSet}
    {element : Elements.LegalElement wrong}
    (registry : Coherence.AtomicCaseRegistry)
    (caseContext : Ontology.StableId)
    (base : SourceConditioned.SourceConditionedElementRequirement bundle facts element) : Set₁ where
  constructor registered-source-conditioned-element-requirement
  field
    registeredAuthorityRule :
      RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
        registry
        caseContext
        (SourceConditioned.authorityRuleApplication base)
    registrationReference : String

open RegisteredSourceConditionedElementRequirement public

record RegisteredSourceConditionedViolation
    {state : Status.SemanticCommitmentState}
    {wrong : Ontology.WrongType}
    {bundle : Elements.WrongTypeRuleBundle wrong}
    {facts : Algebra.FactSet}
    (registry : Coherence.AtomicCaseRegistry)
    (caseContext : Ontology.StableId)
    (base : SourceConditioned.SourceConditionedViolation {state} wrong bundle facts) : Set₁ where
  constructor registered-source-conditioned-violation
  field
    registeredApplicability :
      RegisteredSourceConditionedApplicability
        registry
        caseContext
        (SourceConditioned.applicability base)
    registeredElementRequirements :
      ∀ {element} →
      (membership : element Algebra.∈ Elements.elements bundle) →
      RegisteredSourceConditionedElementRequirement
        registry
        caseContext
        (SourceConditioned.sourceConditionedRequirements base membership)
    violationRegistrationReference : String

open RegisteredSourceConditionedViolation public

------------------------------------------------------------------------
-- Projections: registration strengthens case coherence only; it does not create
-- a new legal derivation, authority role, WrongType, or legacy violation receipt.
------------------------------------------------------------------------

registeredApplicabilityProjectsBase :
  ∀ {state graph facts Enabled r registry caseContext}
    {base : SourceConditioned.SourceConditionedApplicability {state} graph facts Enabled r} →
  RegisteredSourceConditionedApplicability registry caseContext base →
  SourceConditioned.SourceConditionedApplicability {state} graph facts Enabled r
registeredApplicabilityProjectsBase {base = base} _ = base

registeredViolationProjectsBase :
  ∀ {state wrong bundle facts registry caseContext}
    {base : SourceConditioned.SourceConditionedViolation {state} wrong bundle facts} →
  RegisteredSourceConditionedViolation registry caseContext base →
  SourceConditioned.SourceConditionedViolation {state} wrong bundle facts
registeredViolationProjectsBase {base = base} _ = base

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RegistrationCreatesApplicability : Set where
data RegistrationCreatesViolation : Set where
data SameCaseRegistryCreatesWrongType : Set where
data RegisteredElementRequirementErasesAuthoritySource : Set where

data BaseSourceConditioningMakesRegistryOptionalForCaseExecution : Set where

registrationDoesNotCreateApplicability : RegistrationCreatesApplicability → ⊥
registrationDoesNotCreateApplicability ()

registrationDoesNotCreateViolation : RegistrationCreatesViolation → ⊥
registrationDoesNotCreateViolation ()

registryDoesNotCreateWrongType : SameCaseRegistryCreatesWrongType → ⊥
registryDoesNotCreateWrongType ()

registeredRequirementDoesNotEraseAuthoritySource :
  RegisteredElementRequirementErasesAuthoritySource → ⊥
registeredRequirementDoesNotEraseAuthoritySource ()

caseExecutionStillNeedsRegistryCoherence :
  BaseSourceConditioningMakesRegistryOptionalForCaseExecution → ⊥
caseExecutionStillNeedsRegistryCoherence ()

record RegisteredApplicabilityViolationBoundary : Set where
  constructor registered-applicability-violation-boundary
  field
    sourceConditionedBaseRetained : Bool
    applicabilityAtomicRulesRegistered : Bool
    everyElementAuthorityRuleRegistered : Bool
    allRegistrationsUseSameCaseContext : Bool
    registryCreatesLegalResult : Bool

canonicalRegisteredApplicabilityViolationBoundary : RegisteredApplicabilityViolationBoundary
canonicalRegisteredApplicabilityViolationBoundary =
  registered-applicability-violation-boundary true true true true false
