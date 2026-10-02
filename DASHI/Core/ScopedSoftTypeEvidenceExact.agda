module DASHI.Core.ScopedSoftTypeEvidenceExact where

-- DASHI extension: proof-relevant scope/applicability evidence and a
-- negative-control witness. Source refs are locators, never proofs that
-- the source was faithfully parsed or independently authenticated.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScopedSoftTypeContractExact as Scoped
import DASHI.Core.ContextIndexedPNFComparisonTransportExact as Base

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

-- A proof of applicability must be supplied independently of a text
-- receipt. A producer may refuse to provide it, in which case the
-- comparison must stay pending or excluded.
record ApplicableViolation {Value : Set}
    (d : Scoped.SingleValueDemand)
    (a b : Scoped.ScopedIncidence Value)
    (Applicable : Scoped.ScopedIncidence Value → Set) : Set where
  constructor applicable-violation
  field
    cardinalityWitness : Scoped.SingleValueCounterexample d a b
    leftApplicable : Applicable a
    rightApplicable : Applicable b
    sourceInspectionReference : String
open ApplicableViolation public

data EvidenceAssessment {Value : Set}
    (d : Scoped.SingleValueDemand)
    (a b : Scoped.ScopedIncidence Value)
    (Applicable : Scoped.ScopedIncidence Value → Set) : Set where
  supportedViolation :
    ApplicableViolation d a b Applicable →
    EvidenceAssessment d a b Applicable
  pendingPremises :
    List String → EvidenceAssessment d a b Applicable
  excludedByContext :
    String → EvidenceAssessment d a b Applicable

-- The judgment is evidence-preserving: it cannot manufacture an
-- applicable violation from absent premise references.
violationSound :
  ∀ {Value : Set}
    {d : Scoped.SingleValueDemand}
    {a b : Scoped.ScopedIncidence Value}
    {Applicable : Scoped.ScopedIncidence Value → Set} →
  ApplicableViolation d a b Applicable →
  Applicable a
violationSound = leftApplicable

violationHasTwoApplicableFacts :
  ∀ {Value : Set}
    {d : Scoped.SingleValueDemand}
    {a b : Scoped.ScopedIncidence Value}
    {Applicable : Scoped.ScopedIncidence Value → Set} →
  ApplicableViolation d a b Applicable →
  Applicable b
violationHasTwoApplicableFacts = rightApplicable

violationHasDistinctValues :
  ∀ {Value : Set}
    {d : Scoped.SingleValueDemand}
    {a b : Scoped.ScopedIncidence Value}
    {Applicable : Scoped.ScopedIncidence Value → Set} →
  ApplicableViolation d a b Applicable →
  Scoped.observedValue a ≢ Scoped.observedValue b
violationHasDistinctValues v =
  Scoped.valuesDistinct (cardinalityWitness v)

pendingIsNotViolation :
  ∀ {Value : Set}
    {d : Scoped.SingleValueDemand}
    {a b : Scoped.ScopedIncidence Value}
    {Applicable : Scoped.ScopedIncidence Value → Set} →
  (debts : List String)
  (v : ApplicableViolation d a b Applicable) →
  EvidenceAssessment.pendingPremises debts ≢
    EvidenceAssessment.supportedViolation v
pendingIsNotViolation debts v ()

-- A negative control is stated on actual typed scope coordinates rather
-- than on arbitrary strings or a QID. Changing scope is not proof of
-- contradiction even if subject/property/value text overlaps.
record TypedFact (Subject Property Scope Value : Set) : Set where
  constructor typed-fact
  field
    subject : Subject
    property : Property
    scope : Scope
    value : Value
open TypedFact public

record TypedDemand (Subject Property Scope : Set) : Set where
  constructor typed-demand
  field
    demandSubject : Subject
    demandProperty : Property
    demandScope : Scope
open TypedDemand public

record TypedViolation
    {Subject Property Scope Value : Set}
    (d : TypedDemand Subject Property Scope)
    (a b : TypedFact Subject Property Scope Value) : Set where
  constructor typed-violation
  field
    subjectA : subject a ≡ demandSubject d
    subjectB : subject b ≡ demandSubject d
    propertyA : property a ≡ demandProperty d
    propertyB : property b ≡ demandProperty d
    scopeA : scope a ≡ demandScope d
    scopeB : scope b ≡ demandScope d
    distinctValues : value a ≢ value b
open TypedViolation public

typedViolationSameScope :
  ∀ {S P K V : Set} {d : TypedDemand S P K}
    {a b : TypedFact S P K V} →
  TypedViolation d a b → scope a ≡ scope b
typedViolationSameScope v =
  Base.transEq (scopeA v) (Base.symEq (scopeB v))

-- An explicit rejected cross-scope fixture:
-- even with the same subject and property, no well-scoped violation
-- can connect a false-scope observation to a true-scope observation.
crossScopeA : TypedFact Bool Bool Bool Bool
crossScopeA = typed-fact true true false false

crossScopeB : TypedFact Bool Bool Bool Bool
crossScopeB = typed-fact true true true true

trueIsNotFalse : true ≡ false → ⊥
trueIsNotFalse ()

crossScopeCannotViolate :
  (d : TypedDemand Bool Bool Bool) →
  TypedViolation d crossScopeA crossScopeB → ⊥
crossScopeCannotViolate d witness =
  trueIsNotFalse (Base.symEq (typedViolationSameScope witness))

-- Even a genuine counterexample does not insert a class assertion,
-- rewrite either source, or authorize a domain edit. Those operations
-- are absent from these constructors by design; a runtime non-promotion
-- check is still separately necessary.
