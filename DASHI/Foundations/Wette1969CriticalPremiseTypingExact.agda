module DASHI.Foundations.Wette1969CriticalPremiseTypingExact where

------------------------------------------------------------------------
-- WETTE 1969 CRITICAL PREMISE TYPING
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   printed p.145: rule surface for 9.1.5 and 9.3.24/25;
--   printed p.148: intended meanings of the relators;
--   printed p.155: explanation of premises 24/25 of 9.1.5 and premises 3/4
--                  of 9.3.24/25.
--
-- Source facts used here:
--   * p(w1,w2): predicate-schema judgement;
--   * u_x(w1,w2): distinct-variable-tuple judgement;
--   * freshness relator: w1 is not free in w2 and contains no variable/mark
--     occurring freely in w2;
--   * substitution relator: capture/confusion-free substitution with explicit
--     result;
--   * 9.3.24/25 have four common premises, with premise 3 supplying freshness
--     and premise 4 the ordered substitution condition;
--   * 9.1.5 premises 24 and 25 are substitution judgements whose order is
--     irrelevant only under the source-stated side conditions.
--
-- This module types those judgement *kinds*.  It does not claim that the full
-- symbolic bodies of those premises have already been transcribed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RulePremiseTypingGeometryExact as Typing
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical

------------------------------------------------------------------------
-- Formula classification is already supplied by the historical signature:
-- every formula carries exactly one historical relator.
------------------------------------------------------------------------

formulaKind : Signature.Formula → Signature.HistoricalRelator
formulaKind = Signature.relator

------------------------------------------------------------------------
-- 9.3.24/25: source-level four-premise typing specification.
------------------------------------------------------------------------

rule9324x25PremiseTypeSpecification :
  Typing.RulePremiseTypeSpecification Signature.HistoricalRelator
rule9324x25PremiseTypeSpecification =
  Typing.rulePremiseTypeSpecification
    Critical.Premise9324x25
    required
  where
    required : Critical.Premise9324x25 → Signature.HistoricalRelator
    required Critical.recursivePredicateFormation =
      Signature.predicateSchemaRelator
    required Critical.freshVariableTupleFormation =
      Signature.distinctVariableTupleRelator
    required Critical.variableFreshnessCondition =
      Signature.freeForSyntaxRelator
    required Critical.orderedSubstitutionCondition =
      Signature.substitutionRelator

------------------------------------------------------------------------
-- 9.1.5: the two premises singled out by Wette as substitution operations.
------------------------------------------------------------------------

data Rule915SubstitutionSlot : Set where
  premise24 : Rule915SubstitutionSlot
  premise25 : Rule915SubstitutionSlot

rule915Premises24x25TypeSpecification :
  Typing.RulePremiseTypeSpecification Signature.HistoricalRelator
rule915Premises24x25TypeSpecification =
  Typing.rulePremiseTypeSpecification
    Rule915SubstitutionSlot
    (λ _ → Signature.substitutionRelator)

------------------------------------------------------------------------
-- Partial recovery receipt: this records classification only.  Exact formula
-- arguments remain a later transcription obligation.
------------------------------------------------------------------------

data RecoveredCriticalJudgement : Set where
  r9324x25PredicateFormation : RecoveredCriticalJudgement
  r9324x25DistinctTuple : RecoveredCriticalJudgement
  r9324x25Freshness : RecoveredCriticalJudgement
  r9324x25Substitution : RecoveredCriticalJudgement

rule9324x25TypingReceipt :
  Typing.PartialPremiseTypingReceipt
    (Typing.requiredKind rule9324x25PremiseTypeSpecification)
rule9324x25TypingReceipt =
  Typing.partialPremiseTypingReceipt
    RecoveredCriticalJudgement
    include
    recovered
    agrees
  where
    include :
      RecoveredCriticalJudgement → Critical.Premise9324x25
    include r9324x25PredicateFormation = Critical.recursivePredicateFormation
    include r9324x25DistinctTuple = Critical.freshVariableTupleFormation
    include r9324x25Freshness = Critical.variableFreshnessCondition
    include r9324x25Substitution = Critical.orderedSubstitutionCondition

    recovered :
      RecoveredCriticalJudgement → Signature.HistoricalRelator
    recovered r9324x25PredicateFormation = Signature.predicateSchemaRelator
    recovered r9324x25DistinctTuple = Signature.distinctVariableTupleRelator
    recovered r9324x25Freshness = Signature.freeForSyntaxRelator
    recovered r9324x25Substitution = Signature.substitutionRelator

    agrees :
      (slot : RecoveredCriticalJudgement) →
      recovered slot ≡
        Typing.requiredKind rule9324x25PremiseTypeSpecification (include slot)
    agrees r9324x25PredicateFormation = refl
    agrees r9324x25DistinctTuple = refl
    agrees r9324x25Freshness = refl
    agrees r9324x25Substitution = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Wette1969CriticalPremiseTypingBoundary : Set where
  constructor wette1969CriticalPremiseTypingBoundary
  field
    historicalRelatorMeaningsRecoveredFromPrimaryText : Bool
    historicalRelatorMeaningsRecoveredFromPrimaryTextIsTrue :
      historicalRelatorMeaningsRecoveredFromPrimaryText ≡ true

    rule9324x25FourPremiseKindsRecovered : Bool
    rule9324x25FourPremiseKindsRecoveredIsTrue :
      rule9324x25FourPremiseKindsRecovered ≡ true

    rule915Premises24x25TypedAsSubstitutionJudgements : Bool
    rule915Premises24x25TypedAsSubstitutionJudgementsIsTrue :
      rule915Premises24x25TypedAsSubstitutionJudgements ≡ true

    judgementKindRecoveryAlreadySuppliesExactFormulaArguments : Bool
    judgementKindRecoveryAlreadySuppliesExactFormulaArgumentsIsFalse :
      judgementKindRecoveryAlreadySuppliesExactFormulaArguments ≡ false

    premiseTypingAlreadySuppliesExecutableSubstitution : Bool
    premiseTypingAlreadySuppliesExecutableSubstitutionIsFalse :
      premiseTypingAlreadySuppliesExecutableSubstitution ≡ false

canonicalWette1969CriticalPremiseTypingBoundary :
  Wette1969CriticalPremiseTypingBoundary
canonicalWette1969CriticalPremiseTypingBoundary =
  wette1969CriticalPremiseTypingBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
