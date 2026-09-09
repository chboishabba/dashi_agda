module DASHI.Cognition.PNF.SensibLawRegisteredTypedLiabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact as RegisteredImplication
import DASHI.Cognition.PNF.SensibLawRegisteredApplicabilityViolationExact as RegisteredViolation
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawSourceConditionedTypedLiabilityExact as Typed

------------------------------------------------------------------------
-- REGISTERED SOURCE-CONDITIONED TYPED LIABILITY
--
-- One finite case registry spans the entire executable liability chain:
-- violation, family recognition, family conditions, limitations/defeaters,
-- temporal validity and forum competence.  Source attribution and derivation
-- remain owned by the underlying source-conditioned decision; registration only
-- prevents conflicting same-case atomic outcomes from being substituted later.
------------------------------------------------------------------------

record RegisteredSourceConditionedTypedLiabilityDecision
    {state wrong bundle facts}
    {liabilityGraph : Algebra.LegalGraph}
    {profile : Downstream.TypedLiabilityProfile wrong}
    {realised : Typed.SourceConditionedTypedLiabilityProfile profile}
    (registry : Coherence.AtomicCaseRegistry)
    (caseContext : Ontology.StableId)
    (base : Typed.SourceConditionedTypedLiabilityDecision {state} {wrong} {bundle} {facts}
              liabilityGraph profile realised) : Set₁ where
  constructor registered-source-conditioned-typed-liability-decision
  field
    registeredViolation :
      RegisteredViolation.RegisteredSourceConditionedViolation
        registry
        caseContext
        (Typed.sourceConditionedViolation base)

    registeredFamilyRecognitionRule :
      RegisteredImplication.RegisteredSourceConditionedAtomicLegalImplication
        registry
        caseContext
        (Typed.familyRecognitionImplication base)

    familyEntry :
      Coherence.Entry registry (Typed.familyRecognitionProposition realised)
    familyContextMatches :
      Coherence.contextFor registry familyEntry ≡ caseContext
    familyGateMatchesRegistry :
      Atomic.gate (Typed.familyRecognitionAtom base)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry familyEntry)

    conditionEntry :
      ∀ {p} →
      (membership : p Algebra.∈ Downstream.conditions profile) →
      Coherence.Entry registry p
    conditionContextMatches :
      ∀ {p} (membership : p Algebra.∈ Downstream.conditions profile) →
      Coherence.contextFor registry (conditionEntry membership) ≡ caseContext
    conditionGateMatchesRegistry :
      ∀ {p} (membership : p Algebra.∈ Downstream.conditions profile) →
      Atomic.gate (Typed.conditionAtom base membership)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry (conditionEntry membership))

    limitationEntry :
      ∀ {p} →
      (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) →
      Coherence.Entry registry p
    limitationContextMatches :
      ∀ {p} (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) →
      Coherence.contextFor registry (limitationEntry membership) ≡ caseContext
    limitationGateMatchesRegistry :
      ∀ {p} (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) →
      Atomic.gate (Typed.limitationAtom base membership)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry (limitationEntry membership))

    temporalEntry : Coherence.Entry registry (Typed.temporalPredicate realised)
    temporalContextMatches :
      Coherence.contextFor registry temporalEntry ≡ caseContext
    temporalGateMatchesRegistry :
      Atomic.gate (Typed.temporalAtom base)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry temporalEntry)

    competenceEntry : Coherence.Entry registry (Typed.competencePredicate realised)
    competenceContextMatches :
      Coherence.contextFor registry competenceEntry ≡ caseContext
    competenceGateMatchesRegistry :
      Atomic.gate (Typed.competenceAtom base)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry competenceEntry)

    registrationReference : String

open RegisteredSourceConditionedTypedLiabilityDecision public

registeredTypedLiabilityProjectsBase :
  ∀ {state wrong bundle facts liabilityGraph profile realised registry caseContext}
    {base : Typed.SourceConditionedTypedLiabilityDecision {state} {wrong} {bundle} {facts}
              liabilityGraph profile realised} →
  RegisteredSourceConditionedTypedLiabilityDecision registry caseContext base →
  Typed.SourceConditionedTypedLiabilityDecision {state} {wrong} {bundle} {facts}
    liabilityGraph profile realised
registeredTypedLiabilityProjectsBase {base = base} _ = base

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LiabilityRegistrationCreatesUnderlyingViolation : Set where
data LiabilityRegistrationCreatesFamilyAuthority : Set where
data LiabilityRegistryMayOverrideRegisteredNegative : Set where
data DifferentCaseRegistryMayBeSilentlySubstituted : Set where

decisionRegistrationDoesNotCreateViolation :
  LiabilityRegistrationCreatesUnderlyingViolation → ⊥
decisionRegistrationDoesNotCreateViolation ()

registrationDoesNotCreateFamilyAuthority : LiabilityRegistrationCreatesFamilyAuthority → ⊥
registrationDoesNotCreateFamilyAuthority ()

registryCannotOverrideNegativeByPermission : LiabilityRegistryMayOverrideRegisteredNegative → ⊥
registryCannotOverrideNegativeByPermission ()

differentCaseCannotBeSilentlySubstituted : DifferentCaseRegistryMayBeSilentlySubstituted → ⊥
differentCaseCannotBeSilentlySubstituted ()

record RegisteredTypedLiabilityBoundary : Set where
  constructor registered-typed-liability-boundary
  field
    sourceConditionedDecisionRetained : Bool
    underlyingViolationRegistered : Bool
    familyRuleRegistered : Bool
    everyConditionRegistered : Bool
    everyLimitationRegistered : Bool
    temporalAndCompetenceRegistered : Bool
    registryCreatesLegalResult : Bool

canonicalRegisteredTypedLiabilityBoundary : RegisteredTypedLiabilityBoundary
canonicalRegisteredTypedLiabilityBoundary =
  registered-typed-liability-boundary true true true true true true false
