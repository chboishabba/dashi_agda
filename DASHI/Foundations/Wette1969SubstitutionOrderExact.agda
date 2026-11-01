module DASHI.Foundations.Wette1969SubstitutionOrderExact where

------------------------------------------------------------------------
-- WETTE 1969 SUBSTITUTION-ORDER SURFACE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source locus: printed p.155, section 1.632.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.OrderedSubstitutionGeometryExact as Order
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

data CriticalSubstitutionOperation : Set where
  replaceVariableTuple : CriticalSubstitutionOperation
  replacePredicateMarkByRecursivePredicate : CriticalSubstitutionOperation

rule9324x25RequiredPlan : Order.OrderedOperationPlan CriticalSubstitutionOperation
rule9324x25RequiredPlan =
  Order.orderedOperationPlan
    replaceVariableTuple
    replacePredicateMarkByRecursivePredicate

rule9324x25OrderAssignment : Order.SourceOrderAssignment CriticalSubstitutionOperation
rule9324x25OrderAssignment =
  Order.sourceOrderAssignment rule9324x25RequiredPlan Order.orderRequired

data Rule915SubstitutionOperation : Set where
  replace915VariableTuple : Rule915SubstitutionOperation
  replace915PredicateParameter : Rule915SubstitutionOperation

rule915Premises24x25Plan : Order.OrderedOperationPlan Rule915SubstitutionOperation
rule915Premises24x25Plan =
  Order.orderedOperationPlan replace915VariableTuple replace915PredicateParameter

rule915Premises24x25OrderAssignment :
  Order.SourceOrderAssignment Rule915SubstitutionOperation
rule915Premises24x25OrderAssignment =
  Order.sourceOrderAssignment
    rule915Premises24x25Plan
    Order.orderIndependentUnderConditions

-- The contrast itself is an exact source-level fact: the same calculus uses
-- both a conditionally order-independent substitution pair (9.1.5 premises
-- 24/25) and an order-sensitive pair (9.3.24/25 premise 4).
record SourceOrderContrast : Set where
  constructor sourceOrderContrast
  field
    conditionallyIndependentRule : Revision.HistoricalRuleAddress
    conditionallyIndependentPremiseLeft : Nat
    conditionallyIndependentPremiseRight : Nat
    orderedRuleLeft : Revision.HistoricalRuleAddress
    orderedRuleRight : Revision.HistoricalRuleAddress
    orderedPremise : Nat

canonicalSourceOrderContrast : SourceOrderContrast
canonicalSourceOrderContrast =
  sourceOrderContrast
    Revision.rule9-1-5 24 25
    Revision.rule9-3-24 Revision.rule9-3-25 4

record Wette1969SubstitutionOrderBoundary : Set where
  constructor wette1969SubstitutionOrderBoundary
  field
    rule9324x25OrderRequirementRecovered : Bool
    rule9324x25OrderRequirementRecoveredIsTrue :
      rule9324x25OrderRequirementRecovered ≡ true

    rule915Premises24x25ConditionalOrderIndependenceRecovered : Bool
    rule915Premises24x25ConditionalOrderIndependenceRecoveredIsTrue :
      rule915Premises24x25ConditionalOrderIndependenceRecovered ≡ true

    sourceDistinguishesOrderedAndConditionallyIndependentSubstitution : Bool
    sourceDistinguishesOrderedAndConditionallyIndependentSubstitutionIsTrue :
      sourceDistinguishesOrderedAndConditionallyIndependentSubstitution ≡ true

    sourceOrderRequirementAlreadySuppliesHistoricalSubstitutionEvaluator : Bool
    sourceOrderRequirementAlreadySuppliesHistoricalSubstitutionEvaluatorIsFalse :
      sourceOrderRequirementAlreadySuppliesHistoricalSubstitutionEvaluator ≡ false

    sourceOrderRequirementAlreadyProvesSemanticNonCommutation : Bool
    sourceOrderRequirementAlreadyProvesSemanticNonCommutationIsFalse :
      sourceOrderRequirementAlreadyProvesSemanticNonCommutation ≡ false

canonicalWette1969SubstitutionOrderBoundary : Wette1969SubstitutionOrderBoundary
canonicalWette1969SubstitutionOrderBoundary =
  wette1969SubstitutionOrderBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
