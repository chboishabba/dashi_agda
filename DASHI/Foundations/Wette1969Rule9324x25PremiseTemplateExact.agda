module DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.24/25 PREMISE TEMPLATE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source loci:
--   printed p.145: the four common premises of 9.3.24/25;
--   printed p.148: meanings/arities of p, u_x, freshness and substitution;
--   printed p.155: premise 3 is the freshness guard and premise 4 performs
--                  ordered substitution, with V3 first replacing V2.
--
-- The scan/OCR does not yet justify pretending every compound word occurring
-- in the printed rule has been transcribed character-for-character.  What the
-- source does determine reliably is the argument-sharing skeleton below:
--   * one arity word is shared by the predicate-schema and fresh-tuple premises;
--   * the fresh tuple is also the replacement tuple in premise 4;
--   * premise 3 tests that same fresh tuple against the surrounding definition
--     context;
--   * premise 4 is a four-place substitution judgement with an explicit result.
--
-- This is therefore an exact typed *template* for the source-visible skeleton,
-- not yet the final literal rule body.
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

------------------------------------------------------------------------
-- Source-visible parameter skeleton.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Four typed premise bodies in source order.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- The template is a full realization of the already recovered premise-kind
-- specification.  Notice what is proved: relator classification only.  The
-- parameters are not asserted to be the final character-perfect source terms.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Source-significant argument sharing.
------------------------------------------------------------------------

freshTupleIsPremise2TupleAndPremise4Replacement :
  (parameters : Rule9324x25PremiseParameters) → WordTerm
freshTupleIsPremise2TupleAndPremise4Replacement parameters =
  freshTupleWord parameters

------------------------------------------------------------------------
-- Shared-premise pair -> two atomic historical rule bodies.
--
-- Wette prints 9.3.24 and 9.3.25 after one common list of four premises.  His
-- convention is that this abbreviates two rules.  Once the two conclusion
-- formulae are supplied, the existing HistoricalRuleBody carrier can therefore
-- assemble the pair without introducing a second rule representation.
------------------------------------------------------------------------

record Rule9324x25ConclusionParameters : Set where
  constructor rule9324x25ConclusionParameters
  field
    leftConclusion : Formula
    rightConclusion : Formula

open Rule9324x25ConclusionParameters public

rule9-3-24Template :
  Rule9324x25PremiseParameters →
  Rule9324x25ConclusionParameters →
  RuleBody.HistoricalRuleBody
rule9-3-24Template premises conclusions =
  RuleBody.historicalRuleBody
    Revision.rule9-3-24
    4
    (premiseVector premises)
    (leftConclusion conclusions)

rule9-3-25Template :
  Rule9324x25PremiseParameters →
  Rule9324x25ConclusionParameters →
  RuleBody.HistoricalRuleBody
rule9-3-25Template premises conclusions =
  RuleBody.historicalRuleBody
    Revision.rule9-3-25
    4
    (premiseVector premises)
    (rightConclusion conclusions)

rule9324TemplateHasFourPremises :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.premiseCount (rule9-3-24Template premises conclusions) ≡ 4
rule9324TemplateHasFourPremises premises conclusions = refl

rule9325TemplateHasFourPremises :
  (premises : Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25ConclusionParameters) →
  RuleBody.premiseCount (rule9-3-25Template premises conclusions) ≡ 4
rule9325TemplateHasFourPremises premises conclusions = refl

record Wette1969Rule9324x25PremiseTemplateBoundary : Set where
  constructor wette1969Rule9324x25PremiseTemplateBoundary
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

    sharedPremisePairCanAssembleAtomicRuleBodies : Bool
    sharedPremisePairCanAssembleAtomicRuleBodiesIsTrue :
      sharedPremisePairCanAssembleAtomicRuleBodies ≡ true

    parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscription : Bool
    parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscriptionIsFalse :
      parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscription ≡ false

    premiseTemplateAlreadySuppliesHistoricalConclusionArguments : Bool
    premiseTemplateAlreadySuppliesHistoricalConclusionArgumentsIsFalse :
      premiseTemplateAlreadySuppliesHistoricalConclusionArguments ≡ false

canonicalWette1969Rule9324x25PremiseTemplateBoundary :
  Wette1969Rule9324x25PremiseTemplateBoundary
canonicalWette1969Rule9324x25PremiseTemplateBoundary =
  wette1969Rule9324x25PremiseTemplateBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
