{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRound214Validation where

-- Focused source-side validation root kept separate from the shared R191
-- terminal/measure validation so concurrent BIDI workers do not overwrite one
-- another.  This root contains only the corrected qSource route.

import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124
import DASHI.Physics.YangMills.BalabanSU2CMP98LiteralLinearization as Literal
import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm as Main
import DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRecoveryRound211Exact as R211
import DASHI.Physics.YangMills.BalabanCMP98Equation124GroupedCorrectionRound213Exact as R213
import DASHI.Physics.YangMills.BalabanCMP98LiteralCorrectionGroupingRound214Exact as R214

sourceEquation124TranscriptionOwner = Eq124.cmp98LinearizationSourceExact
executableLinearizationOwner = Literal.cmp98ImplementationDefinitionExact

round211Equation124QSourceRecovery =
  R211.cmp98Equation124QSourceRecoveryRound211Level
round211Equation124ExecutableSameObject =
  R211.cmp98Equation124ExecutableSameObjectCompilerRound211Level
round211LiteralEquation124ExecutableWeld =
  R211.literalCMP98Equation124ExecutableWeldRound211Level

round213GroupedEquation124Correction =
  R213.cmp98Equation124GroupedCorrectionRound213Level
round213GroupedTranscriptionCompiler =
  R213.cmp98Equation124GroupedTranscriptionCompilerRound213Level
round213LiteralCorrectionGrouping =
  R213.literalCMP98Equation124ExecutableCorrectionGroupingRound213Level

round214LiteralCorrectionGrouping =
  R214.cmp98LiteralCorrectionGroupingRound214Level
round214LiteralEquation124FromGroupedCorrection =
  R214.cmp98LiteralEquation124FromGroupedCorrectionRound214Level
round214FourPrintedCorrections =
  R214.literalCMP98FourCorrectionGroupingRound214Level

-- The executable main term is already separately source-owned as CMP98 (125).
blockedMainTermOwner = Main.blockedLinearAverageMainTerm
