module DASHI.Foundations.Wette1969RecursorBindingScopeExact where

------------------------------------------------------------------------
-- WETTE 1969 RECURSOR BINDING-SCOPE GEOMETRY
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   * printed p.153: for the recursive constructor, the effective binding scope
--     is the definiens A; C, P and R are untouched by that binding even though
--     the whole expression is assembled into one predicate skeleton;
--   * the same discussion extends confusion-free substitution from V and /\ to
--     the recursor and says capture can concern a variable or predicate mark in
--     the substitute;
--   * printed p.156, section 1.64: the construction of P/A determines which
--     predicate-mark occurrences are free and which are bound by a generalizer,
--     particularizer, or recursor.
--
-- This module recovers the *scope partition* before attempting a full parser for
-- the OCR-sensitive compound recursor word.  That sequencing is intentional:
-- scope ownership is source-stable, while exact target extraction still needs
-- more transcription.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm

------------------------------------------------------------------------
-- Four semantically named regions of the critical recursive-definition surface.
------------------------------------------------------------------------

data RecursorRegion : Set where
  definitionPrerequisiteRegion : RecursorRegion
  conditionRegion : RecursorRegion
  groundingRelationRegion : RecursorRegion
  definiensRegion : RecursorRegion

recursorBindingActiveIn : RecursorRegion → Bool
recursorBindingActiveIn definitionPrerequisiteRegion = false
recursorBindingActiveIn conditionRegion = false
recursorBindingActiveIn groundingRelationRegion = false
recursorBindingActiveIn definiensRegion = true

bindingDoesNotReachDefinitionPrerequisite :
  recursorBindingActiveIn definitionPrerequisiteRegion ≡ false
bindingDoesNotReachDefinitionPrerequisite = refl

bindingDoesNotReachCondition :
  recursorBindingActiveIn conditionRegion ≡ false
bindingDoesNotReachCondition = refl

bindingDoesNotReachGroundingRelation :
  recursorBindingActiveIn groundingRelationRegion ≡ false
bindingDoesNotReachGroundingRelation = refl

bindingActsInDefiniens :
  recursorBindingActiveIn definiensRegion ≡ true
bindingActsInDefiniens = refl

------------------------------------------------------------------------
-- Source says the recursor can participate in capture of free variables or
-- marks occurring in a substitute.  We record the two target classes without
-- pretending the exact compound recursor word has already been parsed into a
-- decidable binder target.
------------------------------------------------------------------------

data RecursorBindingTargetKind : Set where
  variableBindingTarget : RecursorBindingTargetKind
  predicateMarkBindingTarget : RecursorBindingTargetKind

record RecursorScopeTemplate : Set where
  constructor recursorScopeTemplate
  field
    definitionPrerequisite : WordTerm
    condition : WordTerm
    groundingRelation : WordTerm
    definiens : WordTerm

open RecursorScopeTemplate public

regionWord : RecursorScopeTemplate → RecursorRegion → WordTerm
regionWord template definitionPrerequisiteRegion = definitionPrerequisite template
regionWord template conditionRegion = condition template
regionWord template groundingRelationRegion = groundingRelation template
regionWord template definiensRegion = definiens template

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record Wette1969RecursorBindingScopeBoundary : Set where
  constructor wette1969RecursorBindingScopeBoundary
  field
    recursorScopePartitionNowSourceRecovered : Bool
    recursorScopePartitionNowSourceRecoveredIsTrue :
      recursorScopePartitionNowSourceRecovered ≡ true

    recursorBindingRestrictedToDefiniensRegion : Bool
    recursorBindingRestrictedToDefiniensRegionIsTrue :
      recursorBindingRestrictedToDefiniensRegion ≡ true

    sourceAllowsVariableOrPredicateMarkCaptureAtRecursor : Bool
    sourceAllowsVariableOrPredicateMarkCaptureAtRecursorIsTrue :
      sourceAllowsVariableOrPredicateMarkCaptureAtRecursor ≡ true

    exactRecursorBinderTargetParserNowRecovered : Bool
    exactRecursorBinderTargetParserNowRecoveredIsFalse :
      exactRecursorBinderTargetParserNowRecovered ≡ false

    recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluator : Bool
    recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluatorIsFalse :
      recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluator ≡ false

canonicalWette1969RecursorBindingScopeBoundary :
  Wette1969RecursorBindingScopeBoundary
canonicalWette1969RecursorBindingScopeBoundary =
  wette1969RecursorBindingScopeBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
