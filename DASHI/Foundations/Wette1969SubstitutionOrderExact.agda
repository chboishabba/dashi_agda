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
--
-- Wette explicitly contrasts two situations:
--   * in premises 24 and 25 of 9.1.5 the substitution order is irrelevant,
--     under the stated variable/freeness conditions;
--   * in premise 4 of 9.3.24/25 the order matters: first replace the old
--     variable tuple by the new tuple in the definiens, then replace the
--     predicate mark by the recursively defined predicate.  Reversing that
--     order can also replace variables free in the surrounding data.
--
-- This module transcribes that source-level order requirement.  It does not
-- claim an extensional non-commutation theorem for a yet-unreconstructed
-- historical substitution evaluator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.OrderedSubstitutionGeometryExact as Order
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

------------------------------------------------------------------------
-- The two operations named by Wette's explanation of premise 4 in 9.3.24/25.
------------------------------------------------------------------------

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
  Order.sourceOrderAssignment
    rule9324x25RequiredPlan
    Order.orderRequired

------------------------------------------------------------------------
-- The contrast inside 9.1.5 is source-significant.  Wette says premises 24
-- and 25 are order-independent because the substituted and substituting
-- variable tuples consist of distinct variables and the predicate substitutes
-- contain no anonymously free variables.
------------------------------------------------------------------------

data Rule915SubstitutionOperation : Set where
  replace915VariableTuple : Rule915SubstitutionOperation
  replace915PredicateParameter : Rule915SubstitutionOperation

rule915Premises24x25Plan : Order.OrderedOperationPlan Rule915SubstitutionOperation
rule915Premises24x25Plan =
  Order.orderedOperationPlan
    replace915VariableTuple
    replace915PredicateParameter

rule915Premises24x25OrderAssignment :
  Order.SourceOrderAssignment Rule915SubstitutionOperation
rule915Premises24x25OrderAssignment =
  Order.sourceOrderAssignment
    rule915Premises24x25Plan
    Order.orderIndependentUnderConditions

------------------------------------------------------------------------
-- Source locations are attached explicitly so this object can later connect
-- to the exact formula-body transcription without changing its evidence role.
------------------------------------------------------------------------

record SubstitutionOrderSourceReceipt : Set where
  constructor substitutionOrderSourceReceipt
  field
    recursiveApplicationRuleLeft : Revision.HistoricalRuleAddress
    recursiveApplicationRuleRight : Revision.HistoricalRuleAddress
    orderedPremiseNumber : Nat
    orderIndependentRule : Revision.HistoricalRuleAddress
    orderIndependentPremiseLeft : Nat
    orderIndependentPremiseRight : Nat

canonicalSubstitutionOrderSourceReceipt : SubstitutionOrderSourceReceipt
canonicalSubstitutionOrderSourceReceipt =
  substitutionOrderSourceReceipt
    Revision.rule9-3-24
    Revision.rule9-3-25
    4
    Revision.rule9-1-5
    24
    25

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
