module DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.24/25 COMPLETE TYPED TEMPLATE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   printed p.145: four common premises and two conclusions of 9.3.24/25;
--   printed p.148: meanings/arities of p, u_x, freshness, substitution and L;
--   printed p.155, section 1.632: premise 3 is the freshness guard, premise 4
--     performs ordered substitution, and the pair is described unofficially as
--     the two directions of the relative conditional bisubjunction between the
--     substituted definiens and the recursively defined predicate instance.
--
-- The scan/OCR does not justify pretending every compound word has already
-- been transcribed character-for-character.  What the source does determine
-- reliably is both the argument-sharing skeleton of the four premises and the
-- nested-implication skeleton of the two conclusions.  This module therefore
-- completes the typed rule template and constructs both HistoricalRuleBody
-- values end-to-end, while leaving OCR-sensitive compound words as parameters.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

import DASHI.Core.RulePremiseTypingGeometryExact as Typing
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969CriticalPremiseTypingExact as CriticalTyping
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

WordTerm = Signature.WordTerm
Formula = Signature.Formula

record Rule9324x25PremiseParameters : Set where
  constructor rule9324x25PremiseParameters
  field
    arityWord : WordTerm
    recursivePredicateWord : WordTerm
    freshTupleWord : WordTerm
    freshnessContextWord : WordTerm
    oldTupleWord : WordTerm
    substitutionSourceWord : WordTerm
    substitutionResultWord : WordTerm

open Rule9324x25PremiseParameters public

premiseAt : Rule9324x25PremiseParameters → Critical.Premise9324x25 → Formula
premiseAt parameters Critical.recursivePredicateFormation =
  Judgment.predicateSchema
    (arityWord parameters)
    (recursivePredicateWord parameters)
premiseAt parameters Critical.freshVariableTupleFormation =
  Judgment.distinctVariableTuple
    (arityWord parameters)
    (freshTupleWord parameters)
premiseAt parameters Critical.variableFreshnessCondition =
  Judgment.freeForSyntax
    (freshTupleWord parameters)
    (freshnessContextWord parameters)
premiseAt parameters Critical.orderedSubstitutionCondition =
  Judgment.substitution
    (oldTupleWord parameters)
    (substitutionSourceWord parameters)
    (freshTupleWord parameters)
    (substitutionResultWord parameters)

premiseVector : Rule9324x25PremiseParameters → Vec Formula 4
premiseVector parameters =
  premiseAt parameters Critical.recursivePredicateFormation ∷ᵥ
  premiseAt parameters Critical.freshVariableTupleFormation ∷ᵥ
  premiseAt parameters Critical.variableFreshnessCondition ∷ᵥ
  premiseAt parameters Critical.orderedSubstitutionCondition ∷ᵥ
  []ᵥ

rule9324x25TemplateRealizesPremiseTyping :
  (parameters : Rule9324x25PremiseParameters) →
  Typing.RealizesPremiseTypeSpecification
    CriticalTyping.formulaKind
    CriticalTyping.rule9324x25PremiseTypeSpecification
rule9324x25TemplateRealizesPremiseTyping parameters =
  Typing.realizesPremiseTypeSpecification
    (premiseAt parameters)
    agrees
  where
    agrees :
      (slot : Critical.Premise9324x25) →
      CriticalTyping.formulaKind (premiseAt parameters slot) ≡
        Typing.requiredKind
          CriticalTyping.rule9324x25PremiseTypeSpecification
          slot
    agrees Critical.recursivePredicateFormation = refl
    agrees Critical.freshVariableTupleFormation = refl
    agrees Critical.variableFreshnessCondition = refl
    agrees Critical.orderedSubstitutionCondition = refl

freshTupleIsPremise2TupleAndPremise4Replacement :
  (parameters : Rule9324x25PremiseParameters) → WordTerm
freshTupleIsPremise2TupleAndPremise4Replacement parameters =
  freshTupleWord parameters

------------------------------------------------------------------------
-- Conclusion argument template.
--
-- The printed p.145 conclusions share the outer derivability judgement L and
-- exchange the direction of the innermost implication.  Section 1.632 explains
-- the same pair unofficially as a relative conditional bisubjunction: under
-- U1 and the condition instantiated at the fresh tuple, the substituted
-- definiens U2 and the recursively defined predicate instance imply one another.
------------------------------------------------------------------------

record Rule9324x25ConclusionParameters : Set where
  constructor rule9324x25ConclusionParameters
  field
    hypothesisWord : WordTerm
    conditionAtFreshTupleWord : WordTerm
    substitutedDefiniensWord : WordTerm
    recursivePredicateAtFreshTupleWord : WordTerm

open Rule9324x25ConclusionParameters public

implicationWord : WordTerm → WordTerm → WordTerm
implicationWord left right =
  Signature.binaryWordTerm Signature.implicationFunctor refl left right

conditionalDirection : WordTerm → WordTerm → WordTerm → WordTerm
conditionalDirection condition from to =
  implicationWord condition (implicationWord from to)

rule9-3-24Conclusion : Rule9324x25ConclusionParameters → Formula
rule9-3-24Conclusion parameters =
  Judgment.implies
    (hypothesisWord parameters)
    (conditionalDirection
      (conditionAtFreshTupleWord parameters)
      (substitutedDefiniensWord parameters)
      (recursivePredicateAtFreshTupleWord parameters))

rule9-3-25Conclusion : Rule9324x25ConclusionParameters → Formula
rule9-3-25Conclusion parameters =
  Judgment.implies
    (hypothesisWord parameters)
    (conditionalDirection
      (conditionAtFreshTupleWord parameters)
      (recursivePredicateAtFreshTupleWord parameters)
      (substitutedDefiniensWord parameters))

rule9324ConclusionHasImplicationRelator :
  (parameters : Rule9324x25ConclusionParameters) →
  Signature.relator (rule9-3-24Conclusion parameters)
    ≡ Signature.implicationDerivabilityRelator
rule9324ConclusionHasImplicationRelator parameters = refl

rule9325ConclusionHasImplicationRelator :
  (parameters : Rule9324x25ConclusionParameters) →
  Signature.relator (rule9-3-25Conclusion parameters)
    ≡ Signature.implicationDerivabilityRelator
rule9325ConclusionHasImplicationRelator parameters = refl

------------------------------------------------------------------------
-- End-to-end historical rule bodies.
------------------------------------------------------------------------

rule9-3-24 :
  Rule9324x25PremiseParameters →
  Rule9324x25ConclusionParameters →
  RuleBody.HistoricalRuleBody
rule9-3-24 premises conclusions =
  RuleBody.historicalRuleBody
    Revision.rule9-3-24
    4
    (premiseVector premises)
    (rule9-3-24Conclusion conclusions)

rule9-3-25 :
  Rule9324x25PremiseParameters →
  Rule9324x25ConclusionParameters →
  RuleBody.HistoricalRuleBody
rule9-3-25 premises conclusions =
  RuleBody.historicalRuleBody
    Revision.rule9-3-25
    4
    (premiseVector premises)
    (rule9-3-25Conclusion conclusions)

rule9324HasFourPremises :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.premiseCount (rule9-3-24 premises conclusions) ≡ 4
rule9324HasFourPremises premises conclusions = refl

rule9325HasFourPremises :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.premiseCount (rule9-3-25 premises conclusions) ≡ 4
rule9325HasFourPremises premises conclusions = refl

rule9324HasHistoricalAddress :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.address (rule9-3-24 premises conclusions) ≡ Revision.rule9-3-24
rule9324HasHistoricalAddress premises conclusions = refl

rule9325HasHistoricalAddress :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.address (rule9-3-25 premises conclusions) ≡ Revision.rule9-3-25
rule9325HasHistoricalAddress premises conclusions = refl

record Wette1969Rule9324x25TemplateBoundary : Set where
  constructor wette1969Rule9324x25TemplateBoundary
  field
    fourPremiseTemplateNowConstructible : Bool
    fourPremiseTemplateNowConstructibleIsTrue :
      fourPremiseTemplateNowConstructible ≡ true

    freshTupleSharingAcrossPremises2To4Recovered : Bool
    freshTupleSharingAcrossPremises2To4RecoveredIsTrue :
      freshTupleSharingAcrossPremises2To4Recovered ≡ true

    templateRealizesRecoveredPremiseKinds : Bool
    templateRealizesRecoveredPremiseKindsIsTrue :
      templateRealizesRecoveredPremiseKinds ≡ true

    conclusionDirectionTemplatesRecovered : Bool
    conclusionDirectionTemplatesRecoveredIsTrue :
      conclusionDirectionTemplatesRecovered ≡ true

    bothHistoricalRuleBodiesNowConstructibleEndToEnd : Bool
    bothHistoricalRuleBodiesNowConstructibleEndToEndIsTrue :
      bothHistoricalRuleBodiesNowConstructibleEndToEnd ≡ true

    parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscription : Bool
    parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscriptionIsFalse :
      parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscription ≡ false

    typedRuleBodiesAlreadySupplyExecutableSubstitutionEvaluator : Bool
    typedRuleBodiesAlreadySupplyExecutableSubstitutionEvaluatorIsFalse :
      typedRuleBodiesAlreadySupplyExecutableSubstitutionEvaluator ≡ false

canonicalWette1969Rule9324x25TemplateBoundary :
  Wette1969Rule9324x25TemplateBoundary
canonicalWette1969Rule9324x25TemplateBoundary =
  wette1969Rule9324x25TemplateBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
