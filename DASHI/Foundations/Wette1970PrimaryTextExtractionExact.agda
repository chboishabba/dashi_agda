module DASHI.Foundations.Wette1970PrimaryTextExtractionExact where

------------------------------------------------------------------------
-- WETTE 1970 PRIMARY-TEXT EXTRACTION
--
-- Eduard Wette, "Vom Unendlichen zum Endlichen", Dialectica 24(4),
-- 1970, pp. 303--323. DOI: 10.1111/j.1746-8361.1970.tb01221.x.
--
-- This module records only source-visible facts from the inspected primary
-- text and a clearly separated contemporary-review calibration from Kreisel /
-- Zucker (JSL 37(1), 1972, 203--204, DOI: 10.2307/2272630).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DeductionIndexedInterpretationExact as Indexed

record Wette1970CalculusShape : Set where
  constructor wette1970CalculusShape
  field
    wordConstants : Nat
    wordFunctors : Nat
    compactRuleCount : Nat
    compactRelatorCount : Nat
    backwardDecidableRuleCount : Nat
    backwardDecidableRelatorCount : Nat
    mainRulePremiseCount : Nat

open Wette1970CalculusShape public

wette1970CalculusShape : Wette1970CalculusShape
wette1970CalculusShape =
  wette1970CalculusShape 7 8 97 16 129 17 27

record Wette1970ProgrammeFacts : Set where
  constructor wette1970ProgrammeFacts
  field
    calculusCalledFirstSphereOverNaturalNumbers : Bool
    calculusCalledFirstSphereOverNaturalNumbersIsTrue : calculusCalledFirstSphereOverNaturalNumbers ≡ true
    relativeCompletenessLanguageUsedForCalculusClosure : Bool
    relativeCompletenessLanguageUsedForCalculusClosureIsTrue : relativeCompletenessLanguageUsedForCalculusClosure ≡ true
    finiteProofsToBeCodedAsCompletelyAsPossible : Bool
    finiteProofsToBeCodedAsCompletelyAsPossibleIsTrue : finiteProofsToBeCodedAsCompletelyAsPossible ≡ true
    deductionDependentTypeRegionTOfDUsed : Bool
    deductionDependentTypeRegionTOfDUsedIsTrue : deductionDependentTypeRegionTOfDUsed ≡ true
    finiteZFConsistencyReductionToConstructiveArithmeticClaimed : Bool
    finiteZFConsistencyReductionToConstructiveArithmeticClaimedIsTrue : finiteZFConsistencyReductionToConstructiveArithmeticClaimed ≡ true
    systemInternalConsistencyProofThreatClaimed : Bool
    systemInternalConsistencyProofThreatClaimedIsTrue : systemInternalConsistencyProofThreatClaimed ≡ true
    controlledDirectContradictionDerivationStillNeedsFurtherWork : Bool
    controlledDirectContradictionDerivationStillNeedsFurtherWorkIsTrue : controlledDirectContradictionDerivationStillNeedsFurtherWork ≡ true
    pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheory : Bool
    pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheoryIsTrue : pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheory ≡ true
    transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969 : Bool
    transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969IsFalse : transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969 ≡ false

canonicalWette1970ProgrammeFacts : Wette1970ProgrammeFacts
canonicalWette1970ProgrammeFacts =
  wette1970ProgrammeFacts true refl true refl true refl true refl true refl true refl true refl true refl false refl

record KreiselZucker1972RecoveryFacts : Set where
  constructor kreiselZucker1972RecoveryFacts
  field
    relativeCompletenessReportedAsInterpretability : Bool
    relativeCompletenessReportedAsInterpretabilityIsTrue : relativeCompletenessReportedAsInterpretability ≡ true
    stabilizationReported : Bool
    stabilizationReportedIsTrue : stabilizationReported ≡ true
    transfiniteFunctionalInterpretationReported : Bool
    transfiniteFunctionalInterpretationReportedIsTrue : transfiniteFunctionalInterpretationReported ≡ true
    interpretationMayDependOnDeduction : Bool
    interpretationMayDependOnDeductionIsTrue : interpretationMayDependOnDeduction ≡ true
    pointwiseVsUniformInternalizationDistinctionFlagged : Bool
    pointwiseVsUniformInternalizationDistinctionFlaggedIsTrue : pointwiseVsUniformInternalizationDistinctionFlagged ≡ true
    exactInterpretationFormStatedInReviewedPaper : Bool
    exactInterpretationFormStatedInReviewedPaperIsFalse : exactInterpretationFormStatedInReviewedPaper ≡ false
    authorsSpecificInterpretationCertifiedCorrectByReview : Bool
    authorsSpecificInterpretationCertifiedCorrectByReviewIsFalse : authorsSpecificInterpretationCertifiedCorrectByReview ≡ false

canonicalKreiselZucker1972RecoveryFacts : KreiselZucker1972RecoveryFacts
canonicalKreiselZucker1972RecoveryFacts =
  kreiselZucker1972RecoveryFacts true refl true refl true refl true refl true refl false refl false refl

historicalHauptsatz2NeedsDeductionIndexedInterface : Bool
historicalHauptsatz2NeedsDeductionIndexedInterface = true

historicalHauptsatz2NeedsDeductionIndexedInterfaceIsTrue : historicalHauptsatz2NeedsDeductionIndexedInterface ≡ true
historicalHauptsatz2NeedsDeductionIndexedInterfaceIsTrue = refl

formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 : Bool
formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 = false

formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2IsFalse : formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 ≡ false
formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2IsFalse = refl

pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem : Bool
pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem = false

pointwiseInterpretationProofAlreadySuppliesUniformInternalTheoremIsFalse : pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem ≡ false
pointwiseInterpretationProofAlreadySuppliesUniformInternalTheoremIsFalse = refl

------------------------------------------------------------------------
-- 1970 erratum for the supplied 1969 source.
--
-- Wette's errata on printed p.323 say:
--   S. 158, Zeile 1 v. u.: Implikations-Relator tief stellen.
--
-- Direct inspection of the supplied 1969 PDF resolves the corrected locus:
-- it is footnote 12 on p.158, explaining the switch from the official G1
-- derivability notation to the unofficial turnstile notation used in section 2.
-- It is therefore a notation/provenance correction, not a newly identified
-- premise-18 production rule.  The actual 30 implication rules are 9.3.1--30
-- in the pure rule table on printed p.145.
------------------------------------------------------------------------

record Wette1969P158ImplicationRelatorErratum : Set where
  constructor wette1969P158ImplicationRelatorErratum
  field
    correctedPrintedPage : Nat
    correctedLineFromBottom : Nat
    correctionSaysImplicationRelatorSetLow : Bool
    correctionSaysImplicationRelatorSetLowIsTrue : correctionSaysImplicationRelatorSetLow ≡ true
    correctedOccurrenceIsFootnote12NotationExplanation : Bool
    correctedOccurrenceIsFootnote12NotationExplanationIsTrue : correctedOccurrenceIsFootnote12NotationExplanation ≡ true
    correctedOccurrenceIdentifiesPremise18TerminalRule : Bool
    correctedOccurrenceIdentifiesPremise18TerminalRuleIsFalse : correctedOccurrenceIdentifiesPremise18TerminalRule ≡ false

canonicalWette1969P158ImplicationRelatorErratum : Wette1969P158ImplicationRelatorErratum
canonicalWette1969P158ImplicationRelatorErratum =
  wette1969P158ImplicationRelatorErratum 158 1 true refl true refl false refl

indexedInterpretationBoundaryOwner : Indexed.DeductionIndexedInterpretationBoundary
indexedInterpretationBoundaryOwner = Indexed.canonicalDeductionIndexedInterpretationBoundary
