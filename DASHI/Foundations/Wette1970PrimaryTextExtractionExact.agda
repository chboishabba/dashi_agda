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

------------------------------------------------------------------------
-- Calculus shape stated by Wette in 1970.
------------------------------------------------------------------------

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
  wette1970CalculusShape
    7
    8
    97
    16
    129
    17
    27

------------------------------------------------------------------------
-- Source-level programme facts.
------------------------------------------------------------------------

record Wette1970ProgrammeFacts : Set where
  constructor wette1970ProgrammeFacts
  field
    calculusCalledFirstSphereOverNaturalNumbers : Bool
    calculusCalledFirstSphereOverNaturalNumbersIsTrue :
      calculusCalledFirstSphereOverNaturalNumbers ≡ true

    relativeCompletenessLanguageUsedForCalculusClosure : Bool
    relativeCompletenessLanguageUsedForCalculusClosureIsTrue :
      relativeCompletenessLanguageUsedForCalculusClosure ≡ true

    finiteProofsToBeCodedAsCompletelyAsPossible : Bool
    finiteProofsToBeCodedAsCompletelyAsPossibleIsTrue :
      finiteProofsToBeCodedAsCompletelyAsPossible ≡ true

    deductionDependentTypeRegionTOfDUsed : Bool
    deductionDependentTypeRegionTOfDUsedIsTrue :
      deductionDependentTypeRegionTOfDUsed ≡ true

    finiteZFConsistencyReductionToConstructiveArithmeticClaimed : Bool
    finiteZFConsistencyReductionToConstructiveArithmeticClaimedIsTrue :
      finiteZFConsistencyReductionToConstructiveArithmeticClaimed ≡ true

    systemInternalConsistencyProofThreatClaimed : Bool
    systemInternalConsistencyProofThreatClaimedIsTrue :
      systemInternalConsistencyProofThreatClaimed ≡ true

    controlledDirectContradictionDerivationStillNeedsFurtherWork : Bool
    controlledDirectContradictionDerivationStillNeedsFurtherWorkIsTrue :
      controlledDirectContradictionDerivationStillNeedsFurtherWork ≡ true

    pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheory : Bool
    pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheoryIsTrue :
      pureNumberTheoryProblemPosedViaRelativelyCompleteFiniteNumberTheory ≡ true

    transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969 : Bool
    transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969IsFalse :
      transfiniteTypeTheoriesTOfDPerfectlyCalculusDefinedIn1969 ≡ false

canonicalWette1970ProgrammeFacts : Wette1970ProgrammeFacts
canonicalWette1970ProgrammeFacts =
  wette1970ProgrammeFacts
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Kreisel/Zucker 1972 contemporary-review extraction.
--
-- Their review states that Hauptsatz 2 uses "relativ vollstaendig" in the
-- sense that a classical theory of ordinals can be interpreted in Wette's
-- system.  They describe stabilization + an extension of Goedel's functional
-- interpretation using transfinite types + a switch making interpretation
-- depend on the deduction in which a formula occurs.  They explicitly object
-- that Wette does not separate pointwise interpretation-of-each-deduction from
-- one internal theorem asserting the result uniformly for all deductions.
------------------------------------------------------------------------

record KreiselZucker1972RecoveryFacts : Set where
  constructor kreiselZucker1972RecoveryFacts
  field
    relativeCompletenessReportedAsInterpretability : Bool
    relativeCompletenessReportedAsInterpretabilityIsTrue :
      relativeCompletenessReportedAsInterpretability ≡ true

    stabilizationReported : Bool
    stabilizationReportedIsTrue : stabilizationReported ≡ true

    transfiniteFunctionalInterpretationReported : Bool
    transfiniteFunctionalInterpretationReportedIsTrue :
      transfiniteFunctionalInterpretationReported ≡ true

    interpretationMayDependOnDeduction : Bool
    interpretationMayDependOnDeductionIsTrue :
      interpretationMayDependOnDeduction ≡ true

    pointwiseVsUniformInternalizationDistinctionFlagged : Bool
    pointwiseVsUniformInternalizationDistinctionFlaggedIsTrue :
      pointwiseVsUniformInternalizationDistinctionFlagged ≡ true

    exactInterpretationFormStatedInReviewedPaper : Bool
    exactInterpretationFormStatedInReviewedPaperIsFalse :
      exactInterpretationFormStatedInReviewedPaper ≡ false

    authorsSpecificInterpretationCertifiedCorrectByReview : Bool
    authorsSpecificInterpretationCertifiedCorrectByReviewIsFalse :
      authorsSpecificInterpretationCertifiedCorrectByReview ≡ false

canonicalKreiselZucker1972RecoveryFacts : KreiselZucker1972RecoveryFacts
canonicalKreiselZucker1972RecoveryFacts =
  kreiselZucker1972RecoveryFacts
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Cross-pollination consequence.
--
-- The review's deduction-dependent switch means the historical Hauptsatz-2
-- bridge must not be forced prematurely into a formula-only translation map.
-- It belongs first in the generic deduction-indexed interpretation owner.
------------------------------------------------------------------------

historicalHauptsatz2NeedsDeductionIndexedInterface : Bool
historicalHauptsatz2NeedsDeductionIndexedInterface = true

historicalHauptsatz2NeedsDeductionIndexedInterfaceIsTrue :
  historicalHauptsatz2NeedsDeductionIndexedInterface ≡ true
historicalHauptsatz2NeedsDeductionIndexedInterfaceIsTrue = refl

formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 : Bool
formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 = false

formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2IsFalse :
  formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2 ≡ false
formulaOnlyFiniteCalculusTranslationAlreadyRecoversHauptsatz2IsFalse = refl

pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem : Bool
pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem = false

pointwiseInterpretationProofAlreadySuppliesUniformInternalTheoremIsFalse :
  pointwiseInterpretationProofAlreadySuppliesUniformInternalTheorem ≡ false
pointwiseInterpretationProofAlreadySuppliesUniformInternalTheoremIsFalse = refl

indexedInterpretationBoundaryOwner : Indexed.DeductionIndexedInterpretationBoundary
indexedInterpretationBoundaryOwner = Indexed.canonicalDeductionIndexedInterpretationBoundary
