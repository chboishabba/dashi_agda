{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact where

------------------------------------------------------------------------
-- ROUND103/107: BIDI SOURCE-COORDINATE WELD
--
-- A1/A2 and BC1/BC2 remain the frozen Clay frontier.
--
-- Round105/106 adds the finite first-variation stress representation on the
-- canonical CMP116 metric/source domain.  Round107 adds only the missing
-- finite-to-continuum compiler: finite stress representation does not become
-- the literal continuum `stressTensor Y G` until the first-variation and stress
-- pairing sequences have compatible unique limits.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact as R102
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1
import DASHI.Physics.YangMills.BalabanA2LiteralSameHistoryPrefixSensitivityRound103Exact as A2
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116FirstVariationStressPairingRound105Exact as Stress
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as MetricDomain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanFirstVariationStressContinuumRound107Exact as StressLimit
import DASHI.Physics.YangMills.BalabanCMP109116ConventionTransportRound103Exact as Transport
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact as Shell
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat
import DASHI.Physics.YangMills.BalabanBackgroundHessianMetricVariationBoundaryRound105Exact as Metric

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

rowAShellToCumulativeSameHistorySensitivityRound103Level : ProofLevel
rowAShellToCumulativeSameHistorySensitivityRound103Level =
  A2.a2ShellToCumulativeSensitivityLevel

rowAClosedTubeBanachAssemblyRound103Level : ProofLevel
rowAClosedTubeBanachAssemblyRound103Level =
  R102.rowAClosedTubeBanachAssemblyRound102Level

rowAPhysicalSourceInstantiationRound103Level : ProofLevel
rowAPhysicalSourceInstantiationRound103Level = conditional

------------------------------------------------------------------------
-- BC1 / downstream stress consumer
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

bcSubstitutedActivityFirstVariationRound105Level : ProofLevel
bcSubstitutedActivityFirstVariationRound105Level =
  First.cmp116SubstitutedFirstVariationCompilerLevel

bcMetricToBackgroundFirstVariationTransportRound105Level : ProofLevel
bcMetricToBackgroundFirstVariationTransportRound105Level =
  First.metricToBackgroundFirstVariationTransportLevel

bcStressReusesFirstGradientMarkedShellRound105Level : ProofLevel
bcStressReusesFirstGradientMarkedShellRound105Level =
  Stress.cmp116StressReusesFirstGradientMarkedShellLevel

bcCanonicalMetricSourceDomainRound106Level : ProofLevel
bcCanonicalMetricSourceDomainRound106Level =
  MetricDomain.canonicalMetricSourceDomainPackagingLevel

bcLiteralMetricToSourceDomainRound106Level : ProofLevel
bcLiteralMetricToSourceDomainRound106Level =
  MetricDomain.literalMetricPerturbationToCMP116SourceDomainLevel

bcCanonicalMetricStressRepresentationRound106Level : ProofLevel
bcCanonicalMetricStressRepresentationRound106Level =
  StressRep.canonicalMetricStressRepresentationCompilerLevel

bcLiteralMetricStressRepresentationRound106Level : ProofLevel
bcLiteralMetricStressRepresentationRound106Level =
  StressRep.literalCMP116MetricStressRepresentationLevel

bcStressContinuumCompilerRound107Level : ProofLevel
bcStressContinuumCompilerRound107Level =
  StressLimit.stressContinuumCompilerLevel

bcLiteralFirstVariationContinuumInterchangeRound107Level : ProofLevel
bcLiteralFirstVariationContinuumInterchangeRound107Level =
  StressLimit.literalBalabanFirstVariationContinuumInterchangeLevel

-- Older Round105 aliases remain visible for compatibility.
bcStressMetricSourceCoordinateWeldRound105Level : ProofLevel
bcStressMetricSourceCoordinateWeldRound105Level =
  Stress.literalCMP116MetricSourceCoordinateWeldLevel

bcFirstVariationStressPairingRound105Level : ProofLevel
bcFirstVariationStressPairingRound105Level =
  Stress.literalCMP116FirstVariationStressPairingLevel

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

bcBackgroundHessianToMetricVariationRound105Level : ProofLevel
bcBackgroundHessianToMetricVariationRound105Level =
  Metric.metricVariationTransportFromRound103Level

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
