module DASHI.Foundations.Wette1969Rule34ObjectProducerExact where

------------------------------------------------------------------------
-- WETTE 1969 RULES 3 / 4: OBJECT VARIABLE AND PREDICATE-MARK PRODUCERS
--
-- Printed p.144 and the p.148 intended interpretation identify the canonical
-- word constructions already owned by Wette1969ObjectVariableMarkWordsExact.
-- This module now gives those constructions their historical rule bodies and
-- proof-carrying finite-context applications.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969ObjectVariableMarkWordsExact as ObjectSyntax
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

rule3Address : Revision.HistoricalRuleAddress
rule3Address = Revision.historicalRuleAddress 3 0 0

rule4Address : Revision.HistoricalRuleAddress
rule4Address = Revision.historicalRuleAddress 4 0 0

rule3 : WordTerm → RuleBody.HistoricalRuleBody
rule3 index =
  RuleBody.historicalRuleBody
    rule3Address
    1
    (Judgment.naturalNumber index ∷ᵥ []ᵥ)
    (Judgment.naturalVariable (ObjectSyntax.objectVariableWord index))

rule4 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule4 arity index =
  RuleBody.historicalRuleBody
    rule4Address
    2
    ( Judgment.naturalNumber arity
    ∷ᵥ Judgment.naturalNumber index
    ∷ᵥ []ᵥ )
    (Judgment.predicateMarkArity
      arity
      (ObjectSyntax.predicateMarkWord arity index))

rule3ProducesCanonicalObjectVariable :
  (index : WordTerm) →
  RuleBody.conclusion (rule3 index)
    ≡ Judgment.naturalVariable (ObjectSyntax.objectVariableWord index)
rule3ProducesCanonicalObjectVariable index = refl

rule4ProducesCanonicalPredicateMark :
  (arity index : WordTerm) →
  RuleBody.conclusion (rule4 arity index)
    ≡ Judgment.predicateMarkArity arity
        (ObjectSyntax.predicateMarkWord arity index)
rule4ProducesCanonicalPredicateMark arity index = refl

selectRule3 :
  (context : Context) →
  (index : WordTerm) →
  Judgment.naturalNumber index Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule3 context index evidence =
  PCRA.selectedRuleApplication
    (rule3 index)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context (rule3 index) premises)
  where
    premises : Historical.PremisesHold
      Finite.finiteHistoricalContextSystem context (rule3 index)
    premises Fin.zero = evidence

selectRule4 :
  (context : Context) →
  (arity index : WordTerm) →
  Judgment.naturalNumber arity Finite.∈Context context →
  Judgment.naturalNumber index Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule4 context arity index arityEvidence indexEvidence =
  PCRA.selectedRuleApplication
    (rule4 arity index)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context (rule4 arity index) premises)
  where
    premises : Historical.PremisesHold
      Finite.finiteHistoricalContextSystem context (rule4 arity index)
    premises Fin.zero = arityEvidence
    premises (Fin.suc Fin.zero) = indexEvidence

record Wette1969Rule34ObjectProducerBoundary : Set where
  constructor wette1969Rule34ObjectProducerBoundary
  field
    rule3NowProducesCanonicalObjectVariableHistorically : Bool
    rule3NowProducesCanonicalObjectVariableHistoricallyIsTrue :
      rule3NowProducesCanonicalObjectVariableHistorically ≡ true
    rule4NowProducesCanonicalPredicateMarkHistorically : Bool
    rule4NowProducesCanonicalPredicateMarkHistoricallyIsTrue :
      rule4NowProducesCanonicalPredicateMarkHistorically ≡ true
    objectSyntaxConstructorAloneStillDoesNotSupplyNumberPremises : Bool
    objectSyntaxConstructorAloneStillDoesNotSupplyNumberPremisesIsTrue :
      objectSyntaxConstructorAloneStillDoesNotSupplyNumberPremises ≡ true

canonicalWette1969Rule34ObjectProducerBoundary :
  Wette1969Rule34ObjectProducerBoundary
canonicalWette1969Rule34ObjectProducerBoundary =
  wette1969Rule34ObjectProducerBoundary
    true refl true refl true refl
