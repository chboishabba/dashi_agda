module DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: TYPED TEMPLATES FOR PREMISES 8--27
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Direct inspection of printed p.145 fixes the relator and source-visible
-- argument sharing of the later twenty premises.  Several dense compound words
-- (especially abbreviation expansions and the quantified consequents of 18/27)
-- remain parameters rather than guessed OCR strings.
--
-- This is stronger than twenty arbitrary Formula slots: every slot now has its
-- historical judgement kind fixed, and the source-readable arguments are wired
-- through the same parameters used elsewhere in the rule.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915MajorObligationTemplatesExact as Major

WordTerm = Signature.WordTerm
Formula = Signature.Formula

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

record Rule915LaterParameters : Set where
  constructor rule915LaterParameters
  field
    arityWord : WordTerm

    definitionPrerequisiteWord : WordTerm
    definiensSchemaWord : WordTerm

    predicateMarkW2 : WordTerm
    predicateMarkW3 : WordTerm
    predicateMarkW4 : WordTerm
    predicateMarkW5 : WordTerm

    tupleV2 : WordTerm
    tupleV3 : WordTerm
    tupleV4 : WordTerm

    schemaV1 : WordTerm
    schemaW1 : WordTerm

    -- OCR-dense but source-position-stable compound words.
    premise09Context : WordTerm
    premise14Left : WordTerm
    premise14Right : WordTerm
    premise22Left : WordTerm
    premise22Right : WordTerm

    concatenationV5 : WordTerm

    abbreviation16 : WordTerm
    expansion16 : WordTerm
    abbreviation17 : WordTerm
    expansion17 : WordTerm
    abbreviation26 : WordTerm
    expansion26 : WordTerm

    substitutionResultU4 : WordTerm
    substitutionResultU5 : WordTerm

    predecessorInductionConsequent : WordTerm
    definiensIndependenceConsequent : WordTerm

open Rule915LaterParameters public

majorParameters : Rule915LaterParameters → Major.MajorObligationParameters
majorParameters parameters =
  Major.majorObligationParameters
    (definitionPrerequisiteWord parameters)
    (predecessorInductionConsequent parameters)
    (definiensIndependenceConsequent parameters)

premise08 : Rule915LaterParameters → Formula
premise08 p = Judgment.predicateMarkArity (arityWord p) (predicateMarkW3 p)

premise09 : Rule915LaterParameters → Formula
premise09 p = Judgment.freeForSyntax (predicateMarkW3 p) (premise09Context p)

premise10 : Rule915LaterParameters → Formula
premise10 p = Judgment.distinctVariableTuple (arityWord p) (tupleV3 p)

premise11 : Rule915LaterParameters → Formula
premise11 p = Judgment.distinctVariableTuple (arityWord p) (tupleV4 p)

premise12 : Rule915LaterParameters → Formula
premise12 p = Judgment.freeForSyntax (tupleV3 p) (tupleV4 p)

premise13 : Rule915LaterParameters → Formula
premise13 p = Judgment.freeForSyntax (tupleV3 p) (definitionPrerequisiteWord p)

premise14 : Rule915LaterParameters → Formula
premise14 p = Judgment.freeForSyntax (premise14Left p) (premise14Right p)

premise15 : Rule915LaterParameters → Formula
premise15 p =
  Judgment.juxtapositionResult (tupleV4 p) (tupleV3 p) (concatenationV5 p)

premise16 : Rule915LaterParameters → Formula
premise16 p = Judgment.abbreviates (abbreviation16 p) (expansion16 p)

premise17 : Rule915LaterParameters → Formula
premise17 p = Judgment.abbreviates (abbreviation17 p) (expansion17 p)

premise18 : Rule915LaterParameters → Formula
premise18 p = Major.premise18Template (majorParameters p)

premise19 : Rule915LaterParameters → Formula
premise19 p = Judgment.predicateMarkArity (arityWord p) (predicateMarkW4 p)

premise20 : Rule915LaterParameters → Formula
premise20 p = Judgment.predicateMarkArity (arityWord p) (predicateMarkW5 p)

premise21 : Rule915LaterParameters → Formula
premise21 p = Judgment.freeForSyntax (predicateMarkW4 p) (predicateMarkW5 p)

premise22 : Rule915LaterParameters → Formula
premise22 p = Judgment.freeForSyntax (premise22Left p) (premise22Right p)

premise23 : Rule915LaterParameters → Formula
premise23 p = Judgment.freeForSyntax (tupleV3 p) (definiensSchemaWord p)

-- Printed p.145 makes premises 24/25 particularly useful: both are paired
-- four-place II judgements.  The paired substituend is u W2 V2; the paired
-- replacements are u W4 V3 and u W5 V3 respectively.
premise24 : Rule915LaterParameters → Formula
premise24 p =
  Judgment.substitution
    (juxtapose (predicateMarkW2 p) (tupleV2 p))
    (definiensSchemaWord p)
    (juxtapose (predicateMarkW4 p) (tupleV3 p))
    (substitutionResultU4 p)

premise25 : Rule915LaterParameters → Formula
premise25 p =
  Judgment.substitution
    (juxtapose (predicateMarkW2 p) (tupleV2 p))
    (definiensSchemaWord p)
    (juxtapose (predicateMarkW5 p) (tupleV3 p))
    (substitutionResultU5 p)

premise26 : Rule915LaterParameters → Formula
premise26 p = Judgment.abbreviates (abbreviation26 p) (expansion26 p)

premise27 : Rule915LaterParameters → Formula
premise27 p = Major.premise27Template (majorParameters p)

laterPremise : Rule915LaterParameters → Critical.Premise915 → Formula
laterPremise p Critical.p08 = premise08 p
laterPremise p Critical.p09 = premise09 p
laterPremise p Critical.p10 = premise10 p
laterPremise p Critical.p11 = premise11 p
laterPremise p Critical.p12 = premise12 p
laterPremise p Critical.p13 = premise13 p
laterPremise p Critical.p14 = premise14 p
laterPremise p Critical.p15 = premise15 p
laterPremise p Critical.p16 = premise16 p
laterPremise p Critical.p17 = premise17 p
laterPremise p Critical.p18 = premise18 p
laterPremise p Critical.p19 = premise19 p
laterPremise p Critical.p20 = premise20 p
laterPremise p Critical.p21 = premise21 p
laterPremise p Critical.p22 = premise22 p
laterPremise p Critical.p23 = premise23 p
laterPremise p Critical.p24 = premise24 p
laterPremise p Critical.p25 = premise25 p
laterPremise p Critical.p26 = premise26 p
laterPremise p Critical.p27 = premise27 p
-- These values are ignored when composed through exactFirstSevenTranscription.
laterPremise p Critical.p01 = premise08 p
laterPremise p Critical.p02 = premise08 p
laterPremise p Critical.p03 = premise08 p
laterPremise p Critical.p04 = premise08 p
laterPremise p Critical.p05 = premise08 p
laterPremise p Critical.p06 = premise08 p
laterPremise p Critical.p07 = premise08 p

completeTypedTranscription :
  Rule915.Rule915FirstSevenParameters →
  Rule915LaterParameters →
  Rule915.Rule915PremiseTranscription
completeTypedTranscription firstSeven later =
  Rule915.exactFirstSevenTranscription firstSeven (laterPremise later)

premise24HasHistoricalSubstitutionRelator :
  (p : Rule915LaterParameters) →
  Signature.relator (premise24 p) ≡ Signature.substitutionRelator
premise24HasHistoricalSubstitutionRelator p = refl

premise25HasHistoricalSubstitutionRelator :
  (p : Rule915LaterParameters) →
  Signature.relator (premise25 p) ≡ Signature.substitutionRelator
premise25HasHistoricalSubstitutionRelator p = refl

premise18HasHistoricalLRelator :
  (p : Rule915LaterParameters) →
  Signature.relator (premise18 p) ≡ Signature.implicationDerivabilityRelator
premise18HasHistoricalLRelator p = refl

premise27HasHistoricalLRelator :
  (p : Rule915LaterParameters) →
  Signature.relator (premise27 p) ≡ Signature.implicationDerivabilityRelator
premise27HasHistoricalLRelator p = refl

record Wette1969Rule915LaterPremiseTemplatesBoundary : Set where
  constructor wette1969Rule915LaterPremiseTemplatesBoundary
  field
    allTwentyLaterSlotsNowHaveFixedHistoricalJudgementKinds : Bool
    allTwentyLaterSlotsNowHaveFixedHistoricalJudgementKindsIsTrue :
      allTwentyLaterSlotsNowHaveFixedHistoricalJudgementKinds ≡ true
    premises24And25NowLiteralPairedIITemplates : Bool
    premises24And25NowLiteralPairedIITemplatesIsTrue :
      premises24And25NowLiteralPairedIITemplates ≡ true
    premises18And27UseRecoveredOuterLTemplates : Bool
    premises18And27UseRecoveredOuterLTemplatesIsTrue :
      premises18And27UseRecoveredOuterLTemplates ≡ true
    completeTypedTranscriptionHasNoArbitraryFormulaSlots : Bool
    completeTypedTranscriptionHasNoArbitraryFormulaSlotsIsTrue :
      completeTypedTranscriptionHasNoArbitraryFormulaSlots ≡ true
    denseCompoundWordParametersAreAlreadyCharacterPerfectSourceTranscription : Bool
    denseCompoundWordParametersAreAlreadyCharacterPerfectSourceTranscriptionIsFalse :
      denseCompoundWordParametersAreAlreadyCharacterPerfectSourceTranscription ≡ false

canonicalWette1969Rule915LaterPremiseTemplatesBoundary :
  Wette1969Rule915LaterPremiseTemplatesBoundary
canonicalWette1969Rule915LaterPremiseTemplatesBoundary =
  wette1969Rule915LaterPremiseTemplatesBoundary
    true refl true refl true refl true refl false refl
