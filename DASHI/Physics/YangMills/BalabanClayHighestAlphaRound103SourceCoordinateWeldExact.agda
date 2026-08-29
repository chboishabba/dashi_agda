{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact where

------------------------------------------------------------------------
-- ROUND103: BIDI SOURCE-COORDINATE WELD
--
-- A remains the Round102 two-leaf source cut:
--   A1 literal Ward/five-channel evaluator = CMP109 (5.42), two-sided;
--   A2 same-history cumulative beta sensitivity q<1.
--
-- BC1 is now decomposed without opaque same-object Set sockets:
--   Part-I effective action = Part-II localized PHYSICAL composite sum;
--   finite D² commutes with that finite sum;
--   CMP109 (5.1) = D_B² of the same effective action;
--   therefore Pi/E^(2) = sum of CMP116 physical composite B-Hessians;
--   one common positive analytic radius supplies the differentiated shell;
--   any normalization/projection mismatch must pass the explicit transport.
--
-- Critical correction: CMP116 first writes E(X,U,J,A) and then substitutes
-- A=A(B).  Thus D_B²(E∘A) contains both intrinsic Hessian and substitution
-- curvature terms.  The bare A-Hessian is not silently identified with CMP109.
--
-- BC2: on this strict carrier, the Heat/Doob log-Hessian is the conditional
-- expected static Hessian minus covariance of first gradients on the SAME density.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact as R102
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP109116ConventionTransportRound103Exact as Transport
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact as Shell
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat

------------------------------------------------------------------------
-- A: unchanged shortest literal source cut from Round102
------------------------------------------------------------------------

rowAHistoryUniformTwoSidedBetaRound103Level : ProofLevel
rowAHistoryUniformTwoSidedBetaRound103Level =
  R102.rowAHistoryUniformTwoSidedPointwiseBetaRound102Level

rowARationalFamilyToLiteralCMP109BoundsRound103Level : ProofLevel
rowARationalFamilyToLiteralCMP109BoundsRound103Level =
  R102.rowARationalFamilyToLiteralCMP109BoundsRound102Level

rowAClosedTubeBanachAssemblyRound103Level : ProofLevel
rowAClosedTubeBanachAssemblyRound103Level =
  R102.rowAClosedTubeBanachAssemblyRound102Level

rowAPhysicalSourceInstantiationRound103Level : ProofLevel
rowAPhysicalSourceInstantiationRound103Level = conditional

------------------------------------------------------------------------
-- BC1: literal same differentiated carrier
------------------------------------------------------------------------

bcFiniteSecondVariationSumRound103Level : ProofLevel
bcFiniteSecondVariationSumRound103Level =
  Finite.finiteSecondVariationLinearityLevel

bcPartIIContinuationPackagingRound103Level : ProofLevel
bcPartIIContinuationPackagingRound103Level =
  Continue.cmp109116SourceContinuationPackagingLevel

bcEquation51ToLocalizedHessianRound103Level : ProofLevel
bcEquation51ToLocalizedHessianRound103Level =
  Eq51.cmp109Equation51ToLocalizedHessianCompilerLevel

bcSubstitutedActivityChainRuleRound103Level : ProofLevel
bcSubstitutedActivityChainRuleRound103Level =
  Chain.cmp116PhysicalHessianSplitLevel

bcConventionTransportRound103Level : ProofLevel
bcConventionTransportRound103Level =
  Transport.cmp109116ConventionTransportLevel

bcCommonRadiusPackagingRound103Level : ProofLevel
bcCommonRadiusPackagingRound103Level =
  Radius.cmp116CommonRadiusPackagingLevel

bcStrictLiteralCarrierRound103Level : ProofLevel
bcStrictLiteralCarrierRound103Level =
  Carrier.literalDifferentiatedCarrierAssemblyLevel

bcCMP109EqualsCMP116PhysicalHessianRound103Level : ProofLevel
bcCMP109EqualsCMP116PhysicalHessianRound103Level =
  Carrier.cmp109CMP116PhysicalHessianIdentityLevel

bcPhysicalCompositeHessianMarkedShellRound103Level : ProofLevel
bcPhysicalCompositeHessianMarkedShellRound103Level =
  Shell.physicalCompositeHessianMarkedShellCompilerLevel

bc1LiteralSourceInstantiationRound103Level : ProofLevel
bc1LiteralSourceInstantiationRound103Level = conditional

------------------------------------------------------------------------
-- BC2: same-density Heat/Doob identity
------------------------------------------------------------------------

bc2SameDensityHeatDoobIdentityRound103Level : ProofLevel
bc2SameDensityHeatDoobIdentityRound103Level =
  Heat.sameDensityHeatDoobIdentityWiringLevel

bc2LiteralSameDensityInstantiationRound103Level : ProofLevel
bc2LiteralSameDensityInstantiationRound103Level = conditional

------------------------------------------------------------------------
-- Frozen authority
------------------------------------------------------------------------

round103FrozenResearchCountStillFour = R102.round102FrozenResearchCountStillFour

rowACompletionRound103Level : ProofLevel
rowACompletionRound103Level = conditional

rowBCompletionRound103Level : ProofLevel
rowBCompletionRound103Level = conditional

rowCCompletionRound103Level : ProofLevel
rowCCompletionRound103Level = conditional

rowDCompletionRound103Level : ProofLevel
rowDCompletionRound103Level = conditional
