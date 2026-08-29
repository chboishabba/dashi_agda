{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound112A2MarginalPaidExact where

------------------------------------------------------------------------
-- ROUND112--116 HIGHEST-ALPHA BIDI CUT
--
-- A1/A2 and BC1/BC2 remain the authoritative physical leaves from Round103.
--
-- Round112 paid the marginal mixed-Cauchy/cubic-telescope summation.
-- Round113 paid the explicit irrelevant response-kernel + quartic-injection lane.
-- Round114 constructed the CMP116 common radius from finite normalized demands.
-- Round115 compiled source continuation + Eq.(5.1) + those demands directly into
--          the strict Round103 differentiated carrier.
-- Round116 exposes an even shorter A2 lane: if the existing CMP116 beta-marked
--          differentiated shell is literally the generated-history derivative,
--          its cumulative response is already <= C_beta/2 and supplies the
--          history derivative constant directly.  The Round113 response-kernel
--          construction remains the fallback if that same-object identification
--          is not valid for the literal source mark.
--
-- The remaining cut is therefore dominated by SAME-OBJECT source binding, not
-- by new scalar summability or common-radius analysis.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact as R103
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as A2Marg
import DASHI.Physics.YangMills.BalabanA2WardResponseBidiClosureRound113Exact as A2Bidi
import DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact as A2Marked
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat

------------------------------------------------------------------------
-- A1
------------------------------------------------------------------------

a1Equation51CompilerLevel : ProofLevel
a1Equation51CompilerLevel = A1.a1Equation51FiveChannelSameObjectCompilerLevel

a1LiteralEquation51JetIdentificationLevel : ProofLevel
a1LiteralEquation51JetIdentificationLevel =
  A1.literalCMP109Equation51OffDiagonalJetIdentificationLevel

a1LiteralFiveChannelEvaluatorIdentificationLevel : ProofLevel
a1LiteralFiveChannelEvaluatorIdentificationLevel =
  A1.literalWardFiveChannelEvaluatorIsJetBetaLevel

------------------------------------------------------------------------
-- A2: direct marginal is paid; two equivalent producer routes remain available.
------------------------------------------------------------------------

a2MarginalMixedCauchyCubicTelescopeLevel : ProofLevel
a2MarginalMixedCauchyCubicTelescopeLevel =
  A2Marg.a2MixedCauchyMarginalSensitivityLevel

-- Explicit source-injection -> contractive response fallback.
a2ResponseKernelForwardBudgetLevel : ProofLevel
a2ResponseKernelForwardBudgetLevel =
  A2Bidi.a2ResponseKernelForwardBudgetLevel

a2MarginalPlusIrrelevantSubunitConsumerLevel : ProofLevel
a2MarginalPlusIrrelevantSubunitConsumerLevel =
  A2Bidi.a2MarginalPlusIrrelevantSubunitConsumerLevel

-- Shortest route if CMP116 betaMark is literally the shooting-history derivative.
a2SharedMarkedHistoryDerivativeCompilerLevel : ProofLevel
a2SharedMarkedHistoryDerivativeCompilerLevel =
  A2Marked.a2SharedMarkedHistoryDerivativeCompilerLevel

a2SharedMarkedHistoryToCanonicalGammaLevel : ProofLevel
a2SharedMarkedHistoryToCanonicalGammaLevel =
  A2Marked.a2SharedMarkedHistoryToCanonicalGammaLevel

a2LiteralBetaMarkHistoryIdentificationLevel : ProofLevel
a2LiteralBetaMarkHistoryIdentificationLevel =
  A2Marked.literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel

a2LiteralGeneratedHistoryResponseProducerLevel : ProofLevel
a2LiteralGeneratedHistoryResponseProducerLevel =
  A2Bidi.literalCMP109GeneratedHistoryResponseProducerLevel

a2LiteralMarginalIrrelevantDecompositionLevel : ProofLevel
a2LiteralMarginalIrrelevantDecompositionLevel =
  A2Bidi.literalCMP109BetaDifferenceIsMarginalPlusIrrelevantLevel

------------------------------------------------------------------------
-- BC1: common-radius existence and carrier assembly are now paid together.
------------------------------------------------------------------------

bc1CanonicalCarrierCompilerLevel : ProofLevel
bc1CanonicalCarrierCompilerLevel = BC1.bc1CanonicalCarrierCompilerLevel

bc1GeneratedActionLocalizedSumCompilerLevel : ProofLevel
bc1GeneratedActionLocalizedSumCompilerLevel =
  BC1.bc1GeneratedActionLocalizedSumCompilerLevel

bc1SamePotentialHessianCompilerLevel : ProofLevel
bc1SamePotentialHessianCompilerLevel =
  BC1.bc1SamePotentialHessianCompilerLevel

bc1LiteralCanonicalPhysicalInputsLevel : ProofLevel
bc1LiteralCanonicalPhysicalInputsLevel = BC1.literalBC1CanonicalPhysicalInputsLevel

------------------------------------------------------------------------
-- BC2 unchanged: same-density Heat/Doob identity is already theorem-owned.
------------------------------------------------------------------------

bc2SameDensityHeatDoobCompilerLevel : ProofLevel
bc2SameDensityHeatDoobCompilerLevel = Heat.sameDensityHeatDoobIdentityWiringLevel

------------------------------------------------------------------------
-- Frozen authority remains four until the literal physical leaves are inhabited.
------------------------------------------------------------------------

round116FrozenResearchCountStillFour = R103.round103FrozenResearchCountStillFour

rowACompletionRound116Level : ProofLevel
rowACompletionRound116Level = conditional

rowBCompletionRound116Level : ProofLevel
rowBCompletionRound116Level = conditional

rowCCompletionRound116Level : ProofLevel
rowCCompletionRound116Level = conditional

rowDCompletionRound116Level : ProofLevel
rowDCompletionRound116Level = conditional
