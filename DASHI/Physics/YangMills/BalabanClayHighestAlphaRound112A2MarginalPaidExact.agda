{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound112A2MarginalPaidExact where

------------------------------------------------------------------------
-- ROUND112 HIGHEST-ALPHA CUT
--
-- A1/A2 and BC1/BC2 remain the authoritative physical leaves from Round103.
-- This tranche removes one falsely-open subleaf inside A2:
--
--   local mixed-Cauchy d_g beta_int bound
--   + u = g^{-2} cubic Jacobian
--   + positive-beta cubic telescope
--   ---------------------------------------------------------------
--   cutoff-uniform marginal prefix sensitivity q_marg < 1.
--
-- Therefore A2 no longer asks for a fresh summability theorem for the marginal
-- coupling.  Its remaining physical content is precisely:
--
--   (i) same-history decomposition of the literal CMP109 beta difference into
--       marginal + genuinely irrelevant response;
--  (ii) source-native localized/geometric estimate on the irrelevant response;
-- (iii) enough remaining budget so q_marg + q_irr < 1.
--
-- No Row-A promotion is made here because (i)--(iii) are not yet inhabited by
-- the literal generated trajectory.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact as R103
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as A2Marg
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

a2LiteralMarginalIrrelevantDecompositionLevel : ProofLevel
a2LiteralMarginalIrrelevantDecompositionLevel =
  A2Marg.literalCMP109MarginalPlusIrrelevantDecompositionLevel

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

round112FrozenResearchCountStillFour = R103.round103FrozenResearchCountStillFour

rowACompletionRound112Level : ProofLevel
rowACompletionRound112Level = conditional

rowBCompletionRound112Level : ProofLevel
rowBCompletionRound112Level = conditional

rowCCompletionRound112Level : ProofLevel
rowCCompletionRound112Level = conditional

rowDCompletionRound112Level : ProofLevel
rowDCompletionRound112Level = conditional
