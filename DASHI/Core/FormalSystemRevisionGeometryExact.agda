module DASHI.Core.FormalSystemRevisionGeometryExact where

------------------------------------------------------------------------
-- FORMAL-SYSTEM REVISION GEOMETRY
--
-- Generic owner for source-critical edition/revision changes to a formal
-- calculus.  A revision can alter a signature, rule surface, or presentation
-- while leaving questions of derivational/semantic equivalence as additional
-- proof obligations.
--
-- This is deliberately independent of Wette.  Wette 1969 is one historical
-- instance: the p.193--194 addendum changes a premise condition, adds a relator
-- and rule family, and changes the compact rule count.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record FormalSystemPresentation : Set₁ where
  constructor formalSystemPresentation
  field
    Symbol : Set
    Rule : Set
    symbolCount : Nat
    ruleCount : Nat

open FormalSystemPresentation public

record FormalSystemRevision
    (before after : FormalSystemPresentation) : Set₁ where
  constructor formalSystemRevision
  field
    ChangedSymbol : Set
    ChangedRule : Set
    mapsChangedSymbol : ChangedSymbol → Symbol after
    mapsChangedRule : ChangedRule → Rule after

open FormalSystemRevision public

-- Merely exhibiting a historical revision does not prove that the two
-- presentations generate the same derivations, preserve an interpretation,
-- or are conservative over one another.  Such certificates are explicit.
record DerivationalRevisionCertificate
    (before after : FormalSystemPresentation)
    (revision : FormalSystemRevision before after) : Set₁ where
  constructor derivationalRevisionCertificate
  field
    BeforeDerivation : Set
    AfterDerivation : Set
    translateDerivation : BeforeDerivation → AfterDerivation

record BidirectionalRevisionCertificate
    (before after : FormalSystemPresentation)
    (revision : FormalSystemRevision before after) : Set₁ where
  constructor bidirectionalRevisionCertificate
  field
    forward : DerivationalRevisionCertificate before after revision
    reverse : DerivationalRevisionCertificate after before
      (formalSystemRevision
        (ChangedSymbol revision)
        (ChangedRule revision)
        (λ changed → changed)
        (λ changed → changed))

------------------------------------------------------------------------
-- Positive count balance: useful when a source describes additions/removals
-- but Nat subtraction would obscure the bookkeeping.
------------------------------------------------------------------------

record RuleCountBalance : Set where
  constructor ruleCountBalance
  field
    beforeCount : Nat
    addedCount : Nat
    afterCount : Nat
    removedCount : Nat
    balances : beforeCount + addedCount ≡ afterCount + removedCount

record FormalSystemRevisionBoundary : Set where
  constructor formalSystemRevisionBoundary
  field
    historicalRevisionIsNotDefinitionallyDerivationalEquivalence : Bool
    historicalRevisionIsNotDefinitionallyDerivationalEquivalenceIsTrue :
      historicalRevisionIsNotDefinitionallyDerivationalEquivalence ≡ true

    matchingRuleCountsWouldNotProveSemanticEquivalence : Bool
    matchingRuleCountsWouldNotProveSemanticEquivalenceIsTrue :
      matchingRuleCountsWouldNotProveSemanticEquivalence ≡ true

    countBalanceCanBeRecordedWithoutSubtraction : Bool
    countBalanceCanBeRecordedWithoutSubtractionIsTrue :
      countBalanceCanBeRecordedWithoutSubtraction ≡ true

canonicalFormalSystemRevisionBoundary : FormalSystemRevisionBoundary
canonicalFormalSystemRevisionBoundary =
  formalSystemRevisionBoundary
    true refl
    true refl
    true refl
