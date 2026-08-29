{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact where

------------------------------------------------------------------------
-- ROUND103: BIDI SOURCE-COORDINATE WELD
--
-- A1 is now factored through the actual CMP109 Sect.5 off-diagonal two-jet:
--   actual (5.42) mixed derivative
--     = embedded negative mixed coefficient of the Eq.(5.1) jet,
--   Ward/five-channel evaluator = beta coefficient of that SAME jet,
--   exact mixed-jet extraction -> literal two-sided CMP109 beta bounds.
-- A2 remains the same-history q<1 source sensitivity; all shooting/tuning
-- algebra after that estimate is already theorem-owned.
--
-- BC1:
--   Part-I effective action = Part-II localized PHYSICAL composite sum;
--   D² commutes with the finite localized sum;
--   CMP109 (5.1) = D_B² of the same action;
--   hence Pi/E^(2) = sum of CMP116 physical composite B-Hessians;
--   one common positive analytic radius controls the differentiated shell.
--
-- Critical correction: CMP116 first writes E(X,U,J,A) and then substitutes
-- A=A(B), so D_B²(E∘A) contains intrinsic Hessian plus substitution-curvature
-- term.  Bare A-Hessian is not silently identified with CMP109.
--
-- BC2:
--   Heat/Doob log-Hessian = conditional static Hessian - gradient covariance
-- on the SAME literal finite-cutoff density.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact as R102
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1
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
-- A
------------------------------------------------------------------------

rowAEquation51FiveChannelSameObjectRound103Level : ProofLevel
rowAEquation51FiveChannelSameObjectRound103Level =
  A1.a1Equation51FiveChannelSameObjectCompilerLevel

rowAHistoryUniformTwoSidedBetaRound103Level : ProofLevel
rowAHistoryUniformTwoSidedBetaRound103Level =
  R102.rowAHistoryUniformTwoSidedPointwiseBetaRound102Level

rowARationalFamilyToLiteralCMP109BoundsRound103Level : ProofLevel
rowARationalFamilyToLiteralCMP109BoundsRound103Level =
  R102.rowARationalFamilyToLiteralCMP109BoundsRound102Level

rowAClosedTubeBanachAssemblyRound103Level : ProofLevel
rowAClosedTubeBanachAssemblyRound103Level =
  R102.rowAClosedTubeBanachAssemblyRound102Level

-- Physical A leaves: bind the Eq.(5.1) off-diagonal jet and finite Ward/five-
-- channel evaluator on the SAME generated history, then prove same-history q<1.
rowAPhysicalSourceInstantiationRound103Level : ProofLevel
rowAPhysicalSourceInstantiationRound103Level = conditional

------------------------------------------------------------------------
-- BC1
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
-- BC2
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
