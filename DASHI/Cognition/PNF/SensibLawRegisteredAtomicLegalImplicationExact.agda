module DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as Implication

------------------------------------------------------------------------
-- REGISTERED SOURCE-CONDITIONED ATOMIC LEGAL IMPLICATION
--
-- The base implication already requires primary/source-realised rule structure,
-- canonical source receipts, atomic +/- gates and independent graph derivations.
-- This owner adds same-case outcome coherence: every atom used by the rule must
-- be tied to one entry in a finite AtomicCaseRegistry for the same case context.
------------------------------------------------------------------------

record RegisteredSourceConditionedAtomicLegalImplication
    {graph : Algebra.LegalGraph}
    {facts : Algebra.FactSet}
    {Enabled : Algebra.LegalRule → Set}
    {r : Algebra.LegalRule}
    (registry : Coherence.AtomicCaseRegistry)
    (caseContext : Ontology.StableId)
    (input : Implication.SourceConditionedAtomicLegalImplication graph facts Enabled r) : Set₁ where
  constructor registered-source-conditioned-atomic-legal-implication
  field
    premiseEntry :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.premises r) →
      Coherence.Entry registry p
    premiseContextMatches :
      ∀ {p} (membership : p Algebra.∈ Algebra.premises r) →
      Coherence.contextFor registry (premiseEntry membership) ≡ caseContext
    premiseGateMatchesRegistry :
      ∀ {p} (membership : p Algebra.∈ Algebra.premises r) →
      Atomic.gate (Implication.premiseAtom input membership)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry (premiseEntry membership))

    exceptionEntry :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.exceptions r) →
      Coherence.Entry registry p
    exceptionContextMatches :
      ∀ {p} (membership : p Algebra.∈ Algebra.exceptions r) →
      Coherence.contextFor registry (exceptionEntry membership) ≡ caseContext
    exceptionGateMatchesRegistry :
      ∀ {p} (membership : p Algebra.∈ Algebra.exceptions r) →
      Atomic.gate (Implication.exceptionAtom input membership)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry (exceptionEntry membership))

    defeaterEntry :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.defeaters r) →
      Coherence.Entry registry p
    defeaterContextMatches :
      ∀ {p} (membership : p Algebra.∈ Algebra.defeaters r) →
      Coherence.contextFor registry (defeaterEntry membership) ≡ caseContext
    defeaterGateMatchesRegistry :
      ∀ {p} (membership : p Algebra.∈ Algebra.defeaters r) →
      Atomic.gate (Implication.defeaterAtom input membership)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry (defeaterEntry membership))

    jurisdictionEntry :
      Coherence.Entry registry
        (SourceRule.jurisdictionPredicate (Implication.sourceRealisation input))
    jurisdictionContextMatches :
      Coherence.contextFor registry jurisdictionEntry ≡ caseContext
    jurisdictionGateMatchesRegistry :
      Atomic.gate (Implication.jurisdictionAtom input)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry jurisdictionEntry)

    temporalEntry :
      Coherence.Entry registry
        (SourceRule.temporalPredicate (Implication.sourceRealisation input))
    temporalContextMatches :
      Coherence.contextFor registry temporalEntry ≡ caseContext
    temporalGateMatchesRegistry :
      Atomic.gate (Implication.temporalAtom input)
      ≡ Atomic.gate (Coherence.canonicalTestFor registry temporalEntry)

    registrationReference : String

open RegisteredSourceConditionedAtomicLegalImplication public

------------------------------------------------------------------------
-- Registered negative premise blocks a rule that demands that premise +1.
------------------------------------------------------------------------

registeredNegativePremiseBlocksImplication :
  ∀ {graph facts Enabled r registry caseContext}
    {input : Implication.SourceConditionedAtomicLegalImplication graph facts Enabled r} →
  (registered : RegisteredSourceConditionedAtomicLegalImplication registry caseContext input) →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.premises r) →
  Atomic.gate
    (Coherence.canonicalTestFor registry (premiseEntry registered membership))
    ≡ BT.neg →
  ⊥
registeredNegativePremiseBlocksImplication registered membership canonicalNegative =
  posNotNeg
    (trans
      (sym (Implication.premisePasses _ membership))
      (trans
        (premiseGateMatchesRegistry registered membership)
        canonicalNegative))
  where
    posNotNeg : BT.pos ≡ BT.neg → ⊥
    posNotNeg ()

registeredPositiveExceptionBlocksInactiveExceptionClaim :
  ∀ {graph facts Enabled r registry caseContext}
    {input : Implication.SourceConditionedAtomicLegalImplication graph facts Enabled r} →
  (registered : RegisteredSourceConditionedAtomicLegalImplication registry caseContext input) →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.exceptions r) →
  Atomic.gate
    (Coherence.canonicalTestFor registry (exceptionEntry registered membership))
    ≡ BT.pos →
  ⊥
registeredPositiveExceptionBlocksInactiveExceptionClaim registered membership canonicalPositive =
  negNotPos
    (trans
      (sym (Implication.exceptionFailsToApply _ membership))
      (trans
        (exceptionGateMatchesRegistry registered membership)
        canonicalPositive))
  where
    negNotPos : BT.neg ≡ BT.pos → ⊥
    negNotPos ()

registeredPositiveDefeaterBlocksInactiveDefeaterClaim :
  ∀ {graph facts Enabled r registry caseContext}
    {input : Implication.SourceConditionedAtomicLegalImplication graph facts Enabled r} →
  (registered : RegisteredSourceConditionedAtomicLegalImplication registry caseContext input) →
  ∀ {p} →
  (membership : p Algebra.∈ Algebra.defeaters r) →
  Atomic.gate
    (Coherence.canonicalTestFor registry (defeaterEntry registered membership))
    ≡ BT.pos →
  ⊥
registeredPositiveDefeaterBlocksInactiveDefeaterClaim registered membership canonicalPositive =
  negNotPos
    (trans
      (sym (Implication.defeaterFailsToApply _ membership))
      (trans
        (defeaterGateMatchesRegistry registered membership)
        canonicalPositive))
  where
    negNotPos : BT.neg ≡ BT.pos → ⊥
    negNotPos ()

------------------------------------------------------------------------
-- Registration is coherence, not authority or derivation.
------------------------------------------------------------------------

data RegistryCreatesLegalAuthority : Set where
data RegistryEntryCreatesGraphDerivation : Set where
data RegistrationMayOverridePrimarySource : Set where
data SameContextMeansSameProposition : Set where

registryDoesNotCreateAuthority : RegistryCreatesLegalAuthority → ⊥
registryDoesNotCreateAuthority ()

registryDoesNotCreateDerivation : RegistryEntryCreatesGraphDerivation → ⊥
registryDoesNotCreateDerivation ()

registrationDoesNotOverridePrimarySource : RegistrationMayOverridePrimarySource → ⊥
registrationDoesNotOverridePrimarySource ()

sameContextDoesNotIdentifyPropositions : SameContextMeansSameProposition → ⊥
sameContextDoesNotIdentifyPropositions ()

record RegisteredAtomicImplicationBoundary : Set where
  constructor registered-atomic-implication-boundary
  field
    baseSourceConditionedImplicationRetained : Bool
    everyRuleAtomMustUseRegisteredCaseOutcome : Bool
    registeredNegativePremiseMayBeReintroducedPositive : Bool
    registeredPositiveExceptionMayBeTreatedInactive : Bool
    registryCreatesAuthority : Bool

canonicalRegisteredAtomicImplicationBoundary : RegisteredAtomicImplicationBoundary
canonicalRegisteredAtomicImplicationBoundary =
  registered-atomic-implication-boundary true true false false false
