module DASHI.Foundations.Wette1969Rule8117PredicateMarkFreshnessExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 8.1.17: SAME-ARITY PREDICATE-MARK FRESHNESS
--
-- Printed p.144:
--   k V, W1 != W2 -> J (mark(V,W1)) (mark(V,W2)).
--
-- Together with rule 4 this is the source producer pattern for 9.1.5 premises
-- 19,20,21: two V-place fresh predicate marks and their mutual freshness.
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

rule8-1-17Address : Revision.HistoricalRuleAddress
rule8-1-17Address = Revision.historicalRuleAddress 8 1 17

rule8-1-17 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8-1-17 arity leftIndex rightIndex =
  RuleBody.historicalRuleBody
    rule8-1-17Address
    2
    ( Judgment.naturalNumber arity
    ∷ᵥ Judgment.unequal leftIndex rightIndex
    ∷ᵥ []ᵥ )
    (Judgment.freeForSyntax
      (ObjectSyntax.predicateMarkWord arity leftIndex)
      (ObjectSyntax.predicateMarkWord arity rightIndex))

rule8117ProducesSameArityMarkFreshness :
  (arity leftIndex rightIndex : WordTerm) →
  RuleBody.conclusion (rule8-1-17 arity leftIndex rightIndex)
    ≡ Judgment.freeForSyntax
        (ObjectSyntax.predicateMarkWord arity leftIndex)
        (ObjectSyntax.predicateMarkWord arity rightIndex)
rule8117ProducesSameArityMarkFreshness arity leftIndex rightIndex = refl

selectRule8117 :
  (context : Context) →
  (arity leftIndex rightIndex : WordTerm) →
  Judgment.naturalNumber arity Finite.∈Context context →
  Judgment.unequal leftIndex rightIndex Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8117 context arity leftIndex rightIndex arityEvidence unequalEvidence =
  PCRA.selectedRuleApplication
    (rule8-1-17 arity leftIndex rightIndex)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule8-1-17 arity leftIndex rightIndex) premises)
  where
    premises : Historical.PremisesHold
      Finite.finiteHistoricalContextSystem context
      (rule8-1-17 arity leftIndex rightIndex)
    premises Fin.zero = arityEvidence
    premises (Fin.suc Fin.zero) = unequalEvidence

record Wette1969Rule8117PredicateMarkFreshnessBoundary : Set where
  constructor wette1969Rule8117PredicateMarkFreshnessBoundary
  field
    rule8117NowLiteralHistoricalBody : Bool
    rule8117NowLiteralHistoricalBodyIsTrue :
      rule8117NowLiteralHistoricalBody ≡ true
    sameArityDistinctIndexMarksGainHistoricalFreshness : Bool
    sameArityDistinctIndexMarksGainHistoricalFreshnessIsTrue :
      sameArityDistinctIndexMarksGainHistoricalFreshness ≡ true
    distinctIndicesStillRequireHistoricalInequalityEvidence : Bool
    distinctIndicesStillRequireHistoricalInequalityEvidenceIsTrue :
      distinctIndicesStillRequireHistoricalInequalityEvidence ≡ true

canonicalWette1969Rule8117PredicateMarkFreshnessBoundary :
  Wette1969Rule8117PredicateMarkFreshnessBoundary
canonicalWette1969Rule8117PredicateMarkFreshnessBoundary =
  wette1969Rule8117PredicateMarkFreshnessBoundary
    true refl true refl true refl
