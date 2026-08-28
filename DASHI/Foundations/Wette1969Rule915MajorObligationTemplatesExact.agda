module DASHI.Foundations.Wette1969Rule915MajorObligationTemplatesExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: DECISIVE PREMISES 18 AND 27
--
-- Section 1.632 gives unofficial formulae (1) and (2) and explicitly says:
--   premise 18: C implies the P-conditioned predecessor-induction condition;
--   premise 27: C implies the P-conditioned definiens-independence condition.
--
-- The internal quantified consequents are notation-dense and remain separate
-- source-transcription obligations.  What is source-stable is the outer L
-- judgement and its common antecedent C.  This module fixes exactly that layer
-- without pretending the unofficial display is already a character-perfect
-- transcription of the p.145 pure word.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915

WordTerm = Signature.WordTerm
Formula = Signature.Formula

record MajorObligationParameters : Set where
  constructor majorObligationParameters
  field
    definitionPrerequisite : WordTerm
    predecessorInductionConsequent : WordTerm
    definiensIndependenceConsequent : WordTerm

open MajorObligationParameters public

premise18Template : MajorObligationParameters → Formula
premise18Template parameters =
  Judgment.implies
    (definitionPrerequisite parameters)
    (predecessorInductionConsequent parameters)

premise27Template : MajorObligationParameters → Formula
premise27Template parameters =
  Judgment.implies
    (definitionPrerequisite parameters)
    (definiensIndependenceConsequent parameters)

premise18HasHistoricalLRelator :
  (parameters : MajorObligationParameters) →
  Signature.relator (premise18Template parameters)
    ≡ Signature.implicationDerivabilityRelator
premise18HasHistoricalLRelator parameters = refl

premise27HasHistoricalLRelator :
  (parameters : MajorObligationParameters) →
  Signature.relator (premise27Template parameters)
    ≡ Signature.implicationDerivabilityRelator
premise27HasHistoricalLRelator parameters = refl

sharedDefinitionPrerequisite :
  (parameters : MajorObligationParameters) → WordTerm
sharedDefinitionPrerequisite parameters = definitionPrerequisite parameters

-- Tighten an existing transcription only at the two decisive source-stable
-- slots.  All other positions retain their previous source transcription.
fixMajorObligationSlots :
  MajorObligationParameters →
  Rule915.Rule915PremiseTranscription →
  Rule915.Rule915PremiseTranscription
fixMajorObligationSlots parameters transcription =
  Rule915.rule915PremiseTranscription fixed
  where
    fixed : Critical.Premise915 → Formula
    fixed Critical.p18 = premise18Template parameters
    fixed Critical.p27 = premise27Template parameters
    fixed slot = Rule915.premiseAt transcription slot

premise18NowFixed :
  (parameters : MajorObligationParameters) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  Rule915.premiseAt (fixMajorObligationSlots parameters transcription) Critical.p18
    ≡ premise18Template parameters
premise18NowFixed parameters transcription = refl

premise27NowFixed :
  (parameters : MajorObligationParameters) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  Rule915.premiseAt (fixMajorObligationSlots parameters transcription) Critical.p27
    ≡ premise27Template parameters
premise27NowFixed parameters transcription = refl

record Wette1969Rule915MajorObligationTemplatesBoundary : Set where
  constructor wette1969Rule915MajorObligationTemplatesBoundary
  field
    premise18OuterLShapeNowRecovered : Bool
    premise18OuterLShapeNowRecoveredIsTrue :
      premise18OuterLShapeNowRecovered ≡ true
    premise27OuterLShapeNowRecovered : Bool
    premise27OuterLShapeNowRecoveredIsTrue :
      premise27OuterLShapeNowRecovered ≡ true
    bothMajorObligationsShareDefinitionPrerequisiteAntecedent : Bool
    bothMajorObligationsShareDefinitionPrerequisiteAntecedentIsTrue :
      bothMajorObligationsShareDefinitionPrerequisiteAntecedent ≡ true
    quantifiedConsequentWordsNowLiteralOCRPerfect : Bool
    quantifiedConsequentWordsNowLiteralOCRPerfectIsFalse :
      quantifiedConsequentWordsNowLiteralOCRPerfect ≡ false
    unofficialSemanticDisplayAlreadyEqualsPureRuleWordTranscription : Bool
    unofficialSemanticDisplayAlreadyEqualsPureRuleWordTranscriptionIsFalse :
      unofficialSemanticDisplayAlreadyEqualsPureRuleWordTranscription ≡ false

canonicalWette1969Rule915MajorObligationTemplatesBoundary :
  Wette1969Rule915MajorObligationTemplatesBoundary
canonicalWette1969Rule915MajorObligationTemplatesBoundary =
  wette1969Rule915MajorObligationTemplatesBoundary
    true refl true refl true refl false refl false refl
