{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRound214Validation where

------------------------------------------------------------------------
-- Focused SOURCE-side validation root.
--
-- Historical R211/R213/R214 remain useful diagnostics for comparing the
-- independent five-term Eq.(124) transcription with the current executable
-- real-SU(2) linearized average.  Source inspection showed, however, that the
-- executable nested-radial correction is not by construction the sum of all
-- four printed Eq.(124) residual families.
--
-- Canonical qSource authority therefore moves to R215/R216:
--   Eq.(119) exact path operator
--     -> linear content of Eq.(120)
--     -> Q(V0) by definition (121)
--     -> Path13 source with NO caller-supplied qSource.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124
import DASHI.Physics.YangMills.BalabanSU2CMP98LiteralLinearization as Literal
import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm as Main
import DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRecoveryRound211Exact as R211
import DASHI.Physics.YangMills.BalabanCMP98Equation124GroupedCorrectionRound213Exact as R213
import DASHI.Physics.YangMills.BalabanCMP98LiteralCorrectionGroupingRound214Exact as R214
import DASHI.Physics.YangMills.BalabanCMP98Equation120QSourceRecoveryRound215Exact as R215
import DASHI.Physics.YangMills.BalabanCMP98Path13Equation120DerivedQSourceRound216Exact as R216

-- Independent source/executable diagnostic owners.
sourceEquation124TranscriptionOwner = Eq124.cmp98LinearizationSourceExact
executableLinearizationOwner = Literal.cmp98ImplementationDefinitionExact
blockedMainTermOwner = Main.blockedLinearAverageMainTerm

round211Equation124QSourceRecoveryDiagnostic =
  R211.cmp98Equation124QSourceRecoveryRound211Level
round211Equation124ExecutableSameObjectCompilerDiagnostic =
  R211.cmp98Equation124ExecutableSameObjectCompilerRound211Level
round211LiteralEquation124ExecutableWeldStillConditional =
  R211.literalCMP98Equation124ExecutableWeldRound211Level

round213GroupedEquation124CorrectionDiagnostic =
  R213.cmp98Equation124GroupedCorrectionRound213Level
round213GroupedTranscriptionCompilerDiagnostic =
  R213.cmp98Equation124GroupedTranscriptionCompilerRound213Level
round213FullExecutableCorrectionGroupingNotCanonical =
  R213.literalCMP98Equation124ExecutableCorrectionGroupingRound213Level

round214LiteralGroupingCompilerDiagnostic =
  R214.cmp98LiteralCorrectionGroupingRound214Level
round214LiteralEquation124ConditionalCompilerDiagnostic =
  R214.cmp98LiteralEquation124FromGroupedCorrectionRound214Level
round214FourPrintedCorrectionsNotPromoted =
  R214.literalCMP98FourCorrectionGroupingRound214Level

-- Canonical direct source route.
round215Equation120QSourceRecovery =
  R215.cmp98Equation120QSourceRecoveryRound215Level
round215SamePathCarrier =
  R215.cmp98Equation120SamePathCarrierRound215Level
round215Equation119Preserved =
  R215.cmp98Equation119PreservedUnderQSourceRecoveryRound215Level
round215SelectedPathSemantics =
  R215.literalCMP98Equation120SelectedPathSemanticsRound215Level

-- Strongest Path13-facing route: qSource is absent from the physical input
-- record and is generated from Eq.(120) before the ordinary R193 consumer is
-- constructed.
round216Path13DerivedQSource =
  R216.cmp98Path13Equation120DerivedQSourceRound216Level
round216SamePhysicalRealization =
  R216.cmp98Path13Equation120SamePhysicalRealizationRound216Level
round216SelectedSourceSemantics =
  R216.literalCMP98Path13Equation120SelectedSemanticsRound216Level
