module DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic

lookupAll :
  ∀ {A : Set} {P : A → Set} {x xs} →
  Algebra.All P xs →
  x Algebra.∈ xs →
  P x
lookupAll (px Algebra.∷ pxs) Algebra.here = px
lookupAll (px Algebra.∷ pxs) (Algebra.there membership) =
  lookupAll pxs membership

record SourceConditionedAtomicLegalImplication
    (graph : Algebra.LegalGraph)
    (facts : Algebra.FactSet)
    (Enabled : Algebra.LegalRule → Set)
    (r : Algebra.LegalRule) : Set₁ where
  constructor source-conditioned-atomic-legal-implication
  field
    ruleInGraph : r Algebra.∈ Algebra.rules graph
    ruleEnabled : Enabled r
    sourceRealisation : SourceRule.SourceRealisedLegalRule r

    premiseAtom :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.premises r) →
      Atomic.SourceConditionedAtomicLegalTest p
    premiseAtomUsesCanonicalSource :
      ∀ {p} (membership : p Algebra.∈ Algebra.premises r) →
      Atomic.sourceReceipt (premiseAtom membership)
      ≡ lookupAll (SourceRule.premiseSources sourceRealisation) membership
    premisePasses :
      ∀ {p} (membership : p Algebra.∈ Algebra.premises r) →
      Atomic.gate (premiseAtom membership) ≡ BT.pos
    premiseDerived :
      ∀ {p} →
      p Algebra.∈ Algebra.premises r →
      Algebra.Derivation graph facts Enabled p

    exceptionAtom :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.exceptions r) →
      Atomic.SourceConditionedAtomicLegalTest p
    exceptionAtomUsesCanonicalSource :
      ∀ {p} (membership : p Algebra.∈ Algebra.exceptions r) →
      Atomic.sourceReceipt (exceptionAtom membership)
      ≡ lookupAll (SourceRule.exceptionSources sourceRealisation) membership
    exceptionFailsToApply :
      ∀ {p} (membership : p Algebra.∈ Algebra.exceptions r) →
      Atomic.gate (exceptionAtom membership) ≡ BT.neg
    exceptionNotDerived :
      ∀ {p} →
      p Algebra.∈ Algebra.exceptions r →
      Algebra.Derivation graph facts Enabled p → ⊥

    defeaterAtom :
      ∀ {p} →
      (membership : p Algebra.∈ Algebra.defeaters r) →
      Atomic.SourceConditionedAtomicLegalTest p
    defeaterAtomUsesCanonicalSource :
      ∀ {p} (membership : p Algebra.∈ Algebra.defeaters r) →
      Atomic.sourceReceipt (defeaterAtom membership)
      ≡ lookupAll (SourceRule.defeaterSources sourceRealisation) membership
    defeaterFailsToApply :
      ∀ {p} (membership : p Algebra.∈ Algebra.defeaters r) →
      Atomic.gate (defeaterAtom membership) ≡ BT.neg
    defeaterNotDerived :
      ∀ {p} →
      p Algebra.∈ Algebra.defeaters r →
      Algebra.Derivation graph facts Enabled p → ⊥

    jurisdictionAtom :
      Atomic.SourceConditionedAtomicLegalTest
        (SourceRule.jurisdictionPredicate sourceRealisation)
    jurisdictionAtomUsesCanonicalSource :
      Atomic.sourceReceipt jurisdictionAtom
      ≡ SourceRule.jurisdictionSource sourceRealisation
    jurisdictionPasses : Atomic.gate jurisdictionAtom ≡ BT.pos
    jurisdictionDerived :
      Algebra.Derivation graph facts Enabled
        (SourceRule.jurisdictionPredicate sourceRealisation)

    temporalAtom :
      Atomic.SourceConditionedAtomicLegalTest
        (SourceRule.temporalPredicate sourceRealisation)
    temporalAtomUsesCanonicalSource :
      Atomic.sourceReceipt temporalAtom
      ≡ SourceRule.temporalSource sourceRealisation
    temporalPasses : Atomic.gate temporalAtom ≡ BT.pos
    temporalDerived :
      Algebra.Derivation graph facts Enabled
        (SourceRule.temporalPredicate sourceRealisation)

    implicationReference : String

open SourceConditionedAtomicLegalImplication public

record AtomicImplicationDerivationReceipt
    {graph : Algebra.LegalGraph}
    {facts : Algebra.FactSet}
    {Enabled : Algebra.LegalRule → Set}
    {r : Algebra.LegalRule}
    (input : SourceConditionedAtomicLegalImplication graph facts Enabled r) : Set₁ where
  constructor atomic-implication-derivation-receipt
  field
    allPremises :
      Algebra.All (Algebra.Derivation graph facts Enabled) (Algebra.premises r)
    allExceptionsInactive :
      Algebra.All
        (λ p → Algebra.Derivation graph facts Enabled p → ⊥)
        (Algebra.exceptions r)
    allDefeatersInactive :
      Algebra.All
        (λ p → Algebra.Derivation graph facts Enabled p → ⊥)
        (Algebra.defeaters r)

open AtomicImplicationDerivationReceipt public

compileAtomicLegalImplication :
  ∀ {graph facts Enabled r}
    (input : SourceConditionedAtomicLegalImplication graph facts Enabled r) →
    AtomicImplicationDerivationReceipt input →
    Algebra.Derivation graph facts Enabled (Algebra.conclusion r)
compileAtomicLegalImplication input receipt =
  Algebra.byRule
    (ruleInGraph input)
    (ruleEnabled input)
    (allPremises receipt)
    (allExceptionsInactive receipt)
    (allDefeatersInactive receipt)

conclusionRemainsSourceAttributed :
  ∀ {graph facts Enabled r}
    (input : SourceConditionedAtomicLegalImplication graph facts Enabled r) →
    SourceRule.PropositionSourceReceipt (Algebra.conclusion r)
conclusionRemainsSourceAttributed input =
  SourceRule.conclusionSource (sourceRealisation input)

data NegativeExceptionAtomMeansOppositeRule : Set where
data NegativeDefeaterAtomMeansOppositeRule : Set where
data PositivePremiseAtomAloneProvesConclusion : Set where
data AtomicImplicationCreatesAuthority : Set where
data AtomicFitWitnessIsGraphDerivation : Set where
data UnsourcedConclusionAllowed : Set where

negativeExceptionDoesNotMeanOppositeRule : NegativeExceptionAtomMeansOppositeRule → ⊥
negativeExceptionDoesNotMeanOppositeRule ()

negativeDefeaterDoesNotMeanOppositeRule : NegativeDefeaterAtomMeansOppositeRule → ⊥
negativeDefeaterDoesNotMeanOppositeRule ()

onePositivePremiseDoesNotProveConclusion : PositivePremiseAtomAloneProvesConclusion → ⊥
onePositivePremiseDoesNotProveConclusion ()

atomicImplicationDoesNotCreateAuthority : AtomicImplicationCreatesAuthority → ⊥
atomicImplicationDoesNotCreateAuthority ()

atomicFitDoesNotEqualGraphDerivation : AtomicFitWitnessIsGraphDerivation → ⊥
atomicFitDoesNotEqualGraphDerivation ()

unsourcedConclusionNotAllowed : UnsourcedConclusionAllowed → ⊥
unsourcedConclusionNotAllowed ()

record SourceConditionedAtomicLegalImplicationBoundary : Set where
  constructor source-conditioned-atomic-legal-implication-boundary
  field
    conclusionSourceRequired : Bool
    everyPremiseAtomicAndSourceConditioned : Bool
    everyExceptionAtomicAndSourceConditioned : Bool
    everyDefeaterAtomicAndSourceConditioned : Bool
    negativeMeansFailureOfSameAtom : Bool
    negativeMeansLogicalOpposite : Bool
    jurisdictionAtomicAndSourceConditioned : Bool
    temporalAtomicAndSourceConditioned : Bool
    atomicFitAutomaticallyCreatesDerivation : Bool

canonicalSourceConditionedAtomicLegalImplicationBoundary : SourceConditionedAtomicLegalImplicationBoundary
canonicalSourceConditionedAtomicLegalImplicationBoundary =
  source-conditioned-atomic-legal-implication-boundary
    true true true true true false true true false
