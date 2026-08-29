{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound112A2MarginalPaidExact where

------------------------------------------------------------------------
-- ROUND112/113 HIGHEST-ALPHA CUT
--
-- A1/A2 and BC1/BC2 remain the authoritative physical leaves from Round103.
-- Round112 removed the falsely-open marginal summation subleaf:
--
--   local mixed-Cauchy d_g beta_int bound
--   + u = g^{-2} cubic Jacobian
--   + positive-beta cubic telescope
--   ---------------------------------------------------------------
--   cutoff-uniform marginal prefix sensitivity.
--
-- Round113 then inspected A2 backwards from the actual shooting consumer and
-- found that the repository already owns the stronger irrelevant-response lane:
--
--   r_(n+1) <= R s_n + (1/2) r_n,
--   s_n <= D g_n^4,
--   positive-beta cubic telescope,
--   ---------------------------------------------------------------
--   sum r_j <= 2 R S_total,
--   q_marg + q_history < 1
--
-- under the single Ward/canonical small-coupling gate.
--
-- Hence NO fresh scalar/summability theorem remains inside A2 after the literal
-- response producer is inhabited.  The surviving physical content is exactly:
--
--   (i) identify the direct source sensitivity s_j with the literal preceding-
--       history injection on the generated CMP109/CMP119/CMP122 trajectory;
--  (ii) prove the literal one-step irrelevant/polymer response recurrence on
--       that same trajectory;
-- (iii) identify the actual CMP109 beta difference with the sum of the already-
--       paid marginal response and that propagated irrelevant response.
--
-- No Row-A promotion is made until those same-object source identifications and
-- A1's literal Eq.(5.1)/(5.42) weld are inhabited.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact as R103
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as A2Marg
import DASHI.Physics.YangMills.BalabanA2WardResponseBidiClosureRound113Exact as A2Bidi
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
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
-- A2
------------------------------------------------------------------------

a2MarginalMixedCauchyCubicTelescopeLevel : ProofLevel
a2MarginalMixedCauchyCubicTelescopeLevel =
  A2Marg.a2MixedCauchyMarginalSensitivityLevel

a2ResponseKernelForwardBudgetLevel : ProofLevel
a2ResponseKernelForwardBudgetLevel =
  A2Bidi.a2ResponseKernelForwardBudgetLevel

a2MarginalPlusIrrelevantSubunitConsumerLevel : ProofLevel
a2MarginalPlusIrrelevantSubunitConsumerLevel =
  A2Bidi.a2MarginalPlusIrrelevantSubunitConsumerLevel

a2LiteralGeneratedHistoryResponseProducerLevel : ProofLevel
a2LiteralGeneratedHistoryResponseProducerLevel =
  A2Bidi.literalCMP109GeneratedHistoryResponseProducerLevel

a2LiteralMarginalIrrelevantDecompositionLevel : ProofLevel
a2LiteralMarginalIrrelevantDecompositionLevel =
  A2Bidi.literalCMP109BetaDifferenceIsMarginalPlusIrrelevantLevel

------------------------------------------------------------------------
-- BC1 / BC2 unchanged by this tranche
------------------------------------------------------------------------

bc1CommonRadiusPackagingLevel : ProofLevel
bc1CommonRadiusPackagingLevel = Radius.cmp116CommonRadiusPackagingLevel

bc1LiteralCarrierAssemblyLevel : ProofLevel
bc1LiteralCarrierAssemblyLevel = Carrier.literalDifferentiatedCarrierAssemblyLevel

bc2SameDensityHeatDoobCompilerLevel : ProofLevel
bc2SameDensityHeatDoobCompilerLevel = Heat.sameDensityHeatDoobIdentityWiringLevel

------------------------------------------------------------------------
-- Frozen authority remains four until the literal physical leaves are inhabited.
------------------------------------------------------------------------

round113FrozenResearchCountStillFour = R103.round103FrozenResearchCountStillFour

rowACompletionRound113Level : ProofLevel
rowACompletionRound113Level = conditional

rowBCompletionRound113Level : ProofLevel
rowBCompletionRound113Level = conditional

rowCCompletionRound113Level : ProofLevel
rowCCompletionRound113Level = conditional

rowDCompletionRound113Level : ProofLevel
rowDCompletionRound113Level = conditional
