module DASHI.Foundations.Wette1969RecursorBindingScopeExact where

------------------------------------------------------------------------
-- WETTE 1969 RECURSOR BINDING-SCOPE AND TARGET GEOMETRY
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Source loci:
--   * printed pp.151--153: unofficial recursor notation CPR -1 πx A, with the
--     first recursor argument the juxtaposed binder package πx;
--   * printed p.153: only the definiens A is the recursor Wirkungstück; C, P, R
--     remain outside the πx-binding;
--   * printed p.156, section 1.64: construction determines which mark occurrences
--     are bound by generalizer, particularizer, or recursor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

------------------------------------------------------------------------
-- Four semantically named regions of the recursive-definition surface.
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
-- Exact source-stable binder target.
--
-- In Wette's prefix syntax the binary recursor receives first the Juxtor word
-- `u π x` (predicate mark + variable tuple) and second the definiens A.  Thus the
-- recursor binds *both* components of that first argument, and only inside A.
------------------------------------------------------------------------

record RecursorBinderTarget : Set where
  constructor recursorBinderTarget
  field
    predicateMark : WordTerm
    variableTuple : WordTerm

open RecursorBinderTarget public

binderPackage : RecursorBinderTarget → WordTerm
binderPackage target =
  juxtapose (predicateMark target) (variableTuple target)

recursorCore : RecursorBinderTarget → WordTerm → WordTerm
recursorCore target definiens =
  Signature.binaryWordTerm
    Signature.recursionFunctor refl
    (binderPackage target)
    definiens

record RecursorCoreView (word : WordTerm) : Set where
  constructor recursorCoreView
  field
    target : RecursorBinderTarget
    definiens : WordTerm
    wordIsRecursorCore : word ≡ recursorCore target definiens

open RecursorCoreView public

canonicalRecursorCoreView :
  (target : RecursorBinderTarget) →
  (definiens : WordTerm) →
  RecursorCoreView (recursorCore target definiens)
canonicalRecursorCoreView target definiens =
  recursorCoreView target definiens refl

-- The two binder targets are explicit projections of the first recursor word.
recursorPredicateMarkTarget : RecursorBinderTarget → WordTerm
recursorPredicateMarkTarget = predicateMark

recursorVariableTupleTarget : RecursorBinderTarget → WordTerm
recursorVariableTupleTarget = variableTuple

------------------------------------------------------------------------
-- C/P/R/A scope partition kept separate from the exact recursor core.
------------------------------------------------------------------------

record RecursorScopeTemplate : Set where
  constructor recursorScopeTemplate
  field
    definitionPrerequisite : WordTerm
    condition : WordTerm
    groundingRelation : WordTerm
    target : RecursorBinderTarget
    definiens : WordTerm

open RecursorScopeTemplate public

regionWord : RecursorScopeTemplate → RecursorRegion → WordTerm
regionWord template definitionPrerequisiteRegion = definitionPrerequisite template
regionWord template conditionRegion = condition template
regionWord template groundingRelationRegion = groundingRelation template
regionWord template definiensRegion = definiens template

scopeRecursorCore : RecursorScopeTemplate → WordTerm
scopeRecursorCore template = recursorCore (target template) (definiens template)

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

    exactRecursorBinderPackagePiXRecovered : Bool
    exactRecursorBinderPackagePiXRecoveredIsTrue :
      exactRecursorBinderPackagePiXRecovered ≡ true

    predicateMarkAndVariableTupleTargetsSeparated : Bool
    predicateMarkAndVariableTupleTargetsSeparatedIsTrue :
      predicateMarkAndVariableTupleTargetsSeparated ≡ true

    exactRecursorBinderTargetParserNowRecovered : Bool
    exactRecursorBinderTargetParserNowRecoveredIsTrue :
      exactRecursorBinderTargetParserNowRecovered ≡ true

    recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluator : Bool
    recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluatorIsFalse :
      recursorScopePartitionAlreadySuppliesCaptureAvoidingEvaluator ≡ false

    wholeCPRPrefixIsInsideRecursorBindingScope : Bool
    wholeCPRPrefixIsInsideRecursorBindingScopeIsFalse :
      wholeCPRPrefixIsInsideRecursorBindingScope ≡ false

canonicalWette1969RecursorBindingScopeBoundary :
  Wette1969RecursorBindingScopeBoundary
canonicalWette1969RecursorBindingScopeBoundary =
  wette1969RecursorBindingScopeBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
