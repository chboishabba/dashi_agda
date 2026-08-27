module DASHI.Foundations.Wette1969SubstitutionRuleSpineExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

WordTerm = Signature.WordTerm

unary : Signature.HistoricalFunctor → WordTerm → WordTerm
unary functor term = Signature.unaryWordTerm functor refl term

binary : Signature.HistoricalFunctor → WordTerm → WordTerm → WordTerm
binary functor left right = Signature.binaryWordTerm functor refl left right

ruleAddress : Nat → Revision.HistoricalRuleAddress
ruleAddress item = Revision.historicalRuleAddress 8 2 item

rule8-2-1 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8-2-1 variable replacement =
  RuleBody.historicalRuleBody
    (ruleAddress 1) 1
    (Judgment.naturalVariable variable ∷ᵥ []ᵥ)
    (Judgment.substitution variable variable replacement replacement)

rule8-2-12 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8-2-12 arity mark replacement =
  RuleBody.historicalRuleBody
    (ruleAddress 12) 1
    (Judgment.predicateMarkArity arity mark ∷ᵥ []ᵥ)
    (Judgment.substitution mark mark replacement replacement)

rule8-2-2 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8-2-2 substituend source replacement =
  RuleBody.historicalRuleBody
    (ruleAddress 2) 1
    (Judgment.freeForSyntax substituend source ∷ᵥ []ᵥ)
    (Judgment.substitution substituend source replacement source)

rule8-2-3 :
  WordTerm → WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8-2-3 substituend source replacement result =
  RuleBody.historicalRuleBody
    (ruleAddress 3) 1
    (Judgment.substitution substituend source replacement result ∷ᵥ []ᵥ)
    (Judgment.substitution substituend
      (unary Signature.successorFunctor source)
      replacement
      (unary Signature.successorFunctor result))

binaryCongruenceRule :
  Nat → Signature.HistoricalFunctor →
  WordTerm → WordTerm → WordTerm → WordTerm → WordTerm → WordTerm →
  RuleBody.HistoricalRuleBody
binaryCongruenceRule item functor substituend left right replacement leftResult rightResult =
  RuleBody.historicalRuleBody
    (ruleAddress item) 2
    ( Judgment.substitution substituend left replacement leftResult
    ∷ᵥ Judgment.substitution substituend right replacement rightResult
    ∷ᵥ []ᵥ )
    (Judgment.substitution substituend
      (binary functor left right)
      replacement
      (binary functor leftResult rightResult))

BinaryRuleType : Set
BinaryRuleType =
  WordTerm → WordTerm → WordTerm → WordTerm → WordTerm → WordTerm →
  RuleBody.HistoricalRuleBody

rule8-2-4 : BinaryRuleType
rule8-2-4 = binaryCongruenceRule 4 Signature.juxtapositionFunctor

rule8-2-5 : BinaryRuleType
rule8-2-5 = binaryCongruenceRule 5 Signature.implicationFunctor

rule8-2-6 : BinaryRuleType
rule8-2-6 = binaryCongruenceRule 6 Signature.conjunctionFunctor

rule8-2-7 : BinaryRuleType
rule8-2-7 = binaryCongruenceRule 7 Signature.disjunctionFunctor

binderCongruenceRule :
  Nat → Signature.HistoricalFunctor →
  WordTerm → WordTerm → WordTerm → WordTerm → WordTerm →
  RuleBody.HistoricalRuleBody
binderCongruenceRule item functor binder substituend body replacement result =
  RuleBody.historicalRuleBody
    (ruleAddress item) 3
    ( Judgment.freeForSyntax binder replacement
    ∷ᵥ Judgment.freeForSyntax binder substituend
    ∷ᵥ Judgment.substitution substituend body replacement result
    ∷ᵥ []ᵥ )
    (Judgment.substitution substituend
      (binary functor binder body)
      replacement
      (binary functor binder result))

BinderRuleType : Set
BinderRuleType =
  WordTerm → WordTerm → WordTerm → WordTerm → WordTerm →
  RuleBody.HistoricalRuleBody

rule8-2-9 : BinderRuleType
rule8-2-9 = binderCongruenceRule 9 Signature.particularizationFunctor

rule8-2-10 : BinderRuleType
rule8-2-10 = binderCongruenceRule 10 Signature.generalizationFunctor

rule8-2-11 : BinderRuleType
rule8-2-11 = binderCongruenceRule 11 Signature.recursionFunctor

rule821VariableBaseHasHistoricalII :
  (variable replacement : WordTerm) →
  RuleBody.conclusion (rule8-2-1 variable replacement)
    ≡ Judgment.substitution variable variable replacement replacement
rule821VariableBaseHasHistoricalII variable replacement = refl

rule8212PredicateMarkBaseHasHistoricalII :
  (arity mark replacement : WordTerm) →
  RuleBody.conclusion (rule8-2-12 arity mark replacement)
    ≡ Judgment.substitution mark mark replacement replacement
rule8212PredicateMarkBaseHasHistoricalII arity mark replacement = refl

rule8211IsRecursorBinderCongruence :
  (binder substituend body replacement result : WordTerm) →
  RuleBody.conclusion (rule8-2-11 binder substituend body replacement result)
    ≡ Judgment.substitution substituend
        (binary Signature.recursionFunctor binder body)
        replacement
        (binary Signature.recursionFunctor binder result)
rule8211IsRecursorBinderCongruence binder substituend body replacement result = refl

record Wette1969SubstitutionRuleSpineBoundary : Set where
  constructor wette1969SubstitutionRuleSpineBoundary
  field
    variableAndPredicateMarkBaseRulesRecovered : Bool
    variableAndPredicateMarkBaseRulesRecoveredIsTrue :
      variableAndPredicateMarkBaseRulesRecovered ≡ true
    unaryAndBinaryCongruenceRulesRecovered : Bool
    unaryAndBinaryCongruenceRulesRecoveredIsTrue :
      unaryAndBinaryCongruenceRulesRecovered ≡ true
    quantifierAndRecursorBinderCongruenceRulesRecovered : Bool
    quantifierAndRecursorBinderCongruenceRulesRecoveredIsTrue :
      quantifierAndRecursorBinderCongruenceRulesRecovered ≡ true
    binderCongruenceRequiresFreshnessPremises : Bool
    binderCongruenceRequiresFreshnessPremisesIsTrue :
      binderCongruenceRequiresFreshnessPremises ≡ true
    recoveredRuleSpineIsAlreadyTotalDecisionProcedure : Bool
    recoveredRuleSpineIsAlreadyTotalDecisionProcedureIsFalse :
      recoveredRuleSpineIsAlreadyTotalDecisionProcedure ≡ false

canonicalWette1969SubstitutionRuleSpineBoundary : Wette1969SubstitutionRuleSpineBoundary
canonicalWette1969SubstitutionRuleSpineBoundary =
  wette1969SubstitutionRuleSpineBoundary
    true refl true refl true refl true refl false refl
