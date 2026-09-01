{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRound214Validation where

------------------------------------------------------------------------
-- Focused SOURCE-side validation root.
--
-- Historical R211/R213/R214 remain useful diagnostics for comparing the
-- independent five-term Eq.(124) transcription with the current executable
-- real-SU(2) linearized average. Source inspection showed, however, that the
-- executable nested-radial correction is not by construction the sum of all
-- four printed Eq.(124) residual families.
--
-- Canonical qSource authority moves to R215/R216:
--   Eq.(119) exact path operator
--     -> linear content of Eq.(120)
--     -> Q(V0) by definition (121)
--     -> Path13 source with NO caller-supplied qSource.
-- R217 decomposes source semantics; R218 then performs repository archaeology
-- and prunes the already-owned principal-Y, cut-radius and path-realization
-- coordinates, leaving only two live same-object source receipts.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124
import DASHI.Physics.YangMills.BalabanSU2CMP98LiteralLinearization as Literal
import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm as Main
import DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRecoveryRound211Exact as R211
import DASHI.Physics.YangMills.BalabanCMP98Equation124GroupedCorrectionRound213Exact as R213
import DASHI.Physics.YangMills.BalabanCMP98LiteralCorrectionGroupingRound214Exact as R214
import DASHI.Physics.YangMills.BalabanCMP98Equation120QSourceRecoveryRound215Exact as R215
import DASHI.Physics.YangMills.BalabanCMP98Path13Equation120DerivedQSourceRound216Exact as R216
import DASHI.Physics.YangMills.BalabanCMP98Equation120SelectedSemanticsRound217Exact as R217
import DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact as R218

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
round215SelectedPathSemanticsHistoricalAggregate =
  R215.literalCMP98Equation120SelectedPathSemanticsRound215Level

round216Path13DerivedQSource =
  R216.cmp98Path13Equation120DerivedQSourceRound216Level
round216SamePhysicalRealization =
  R216.cmp98Path13Equation120SamePhysicalRealizationRound216Level
round216SelectedSourceSemanticsHistoricalAggregate =
  R216.literalCMP98Path13Equation120SelectedSemanticsRound216Level

-- R217 is the structured audit that exposed which subreceipts to search.
round217SelectedSemanticsStructure =
  R217.cmp98Equation120SelectedSemanticsRound217Level
round217SelectedBackgroundReuse =
  R217.cmp98Equation120SelectedBackgroundReuseRound217Level
round217SelectedFederbushReuse =
  R217.cmp98Equation120SelectedFederbushReuseRound217Level

-- R218 is the current source frontier after following R179/R181/R187/R189/R192.
round218RecoveredSourceFrontier =
  R218.cmp98Equation120RecoveredSourceFrontierRound218Level
round218PrincipalYPruned =
  R218.cmp98PrincipalYFrontierPrunedRound218Level
round218SelectedCutRadiusPruned =
  R218.cmp98SelectedCutRadiusFrontierPrunedRound218Level
round218PathRealizationPruned =
  R218.cmp98PathRealizationFrontierPrunedRound218Level
round218Path13SelectedPhysicalBackgroundSameObject =
  R218.literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level
round218PerturbationCoordinateSemantics =
  R218.literalCMP98PerturbationCoordinateSemanticsRound218Level
