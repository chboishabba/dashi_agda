module DASHI.Foundations.Wette1969Rule915MajorPDFSourceAuditExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PDF-EXACT SOURCE AUDIT FOR PREMISES 18 / 27
--
-- Direct inspection of the supplied 1969 scan fixes the relevant printed-page
-- loci and dependency statements.  This module records those source-visible
-- facts only; it does not identify the unofficial displays with the dense pure
-- p.145 words by fiat.
--
-- Source: Eduard Wette, 1969,
-- DOI 10.1007/978-3-642-86745-3_9.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

pureRuleTablePrintedPage : Nat
pureRuleTablePrintedPage = 145

premise18DisplayPrintedPage : Nat
premise18DisplayPrintedPage = 154

premise27DisplayPrintedPage : Nat
premise27DisplayPrintedPage = 155

notationFootnotePrintedPage : Nat
notationFootnotePrintedPage = 158

premise18Slot : Nat
premise18Slot = 18

premise27Slot : Nat
premise27Slot = 27

record Wette1969Rule915MajorPDFSourceAuditBoundary : Set where
  constructor wette1969Rule915MajorPDFSourceAuditBoundary
  field
    p145PrintsComplete915RuleSurface : Bool
    p145PrintsComplete915RuleSurfaceIsTrue :
      p145PrintsComplete915RuleSurface ≡ true

    section1632PrintsPremise18UnofficialFormula : Bool
    section1632PrintsPremise18UnofficialFormulaIsTrue :
      section1632PrintsPremise18UnofficialFormula ≡ true

    premise18MeansCImpliesPConditionedPredecessorInductionRelativeToR : Bool
    premise18MeansCImpliesPConditionedPredecessorInductionRelativeToRIsTrue :
      premise18MeansCImpliesPConditionedPredecessorInductionRelativeToR ≡ true

    premise18GeneralisationUsesPremises13And9 : Bool
    premise18GeneralisationUsesPremises13And9IsTrue :
      premise18GeneralisationUsesPremises13And9 ≡ true

    premise18CollisionAvoidanceAlsoUsesPremises9And14 : Bool
    premise18CollisionAvoidanceAlsoUsesPremises9And14IsTrue :
      premise18CollisionAvoidanceAlsoUsesPremises9And14 ≡ true

    section1632PrintsPremise27UnofficialFormula : Bool
    section1632PrintsPremise27UnofficialFormulaIsTrue :
      section1632PrintsPremise27UnofficialFormula ≡ true

    premise27MeansCImpliesPConditionedDefiniensIndependenceRelativeToR : Bool
    premise27MeansCImpliesPConditionedDefiniensIndependenceRelativeToRIsTrue :
      premise27MeansCImpliesPConditionedDefiniensIndependenceRelativeToR ≡ true

    premise27GeneralisationUsesPremises13And22 : Bool
    premise27GeneralisationUsesPremises13And22IsTrue :
      premise27GeneralisationUsesPremises13And22 ≡ true

    premise27CollisionAvoidanceUsesPremises22And23 : Bool
    premise27CollisionAvoidanceUsesPremises22And23IsTrue :
      premise27CollisionAvoidanceUsesPremises22And23 ≡ true

    p158CorrectedImplicationRelatorOccurrenceIsNotationFootnote : Bool
    p158CorrectedImplicationRelatorOccurrenceIsNotationFootnoteIsTrue :
      p158CorrectedImplicationRelatorOccurrenceIsNotationFootnote ≡ true

    p158ErratumIdentifiesNewPremise18TerminalRule : Bool
    p158ErratumIdentifiesNewPremise18TerminalRuleIsFalse :
      p158ErratumIdentifiesNewPremise18TerminalRule ≡ false

    unofficialDisplaysAlreadyCharacterPerfectPureP145Words : Bool
    unofficialDisplaysAlreadyCharacterPerfectPureP145WordsIsFalse :
      unofficialDisplaysAlreadyCharacterPerfectPureP145Words ≡ false

canonicalWette1969Rule915MajorPDFSourceAuditBoundary :
  Wette1969Rule915MajorPDFSourceAuditBoundary
canonicalWette1969Rule915MajorPDFSourceAuditBoundary =
  wette1969Rule915MajorPDFSourceAuditBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
