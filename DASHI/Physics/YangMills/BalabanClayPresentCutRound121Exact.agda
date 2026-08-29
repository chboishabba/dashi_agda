{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayPresentCutRound121Exact where

------------------------------------------------------------------------
-- ROUND121: PRESENT A/C CUT, BIDI-COMPILED END TO END
--
-- This is the exact cut requested after Round116:
--
-- A1  Eq.(5.1) physical mixed jet = W+Q+R -> five channels -> (5.42)
-- A2  generated-history response; betaMark shortcut only if literally derivative
-- BC1 literal CMP109/CMP116 continuation + finite analytic demand extraction,
--     retaining the full A=A(B) second-variation chain rule
-- BC2 compact-group Heat/Doob on the exact same effective potential.
--
-- Every downstream algebraic/analytic compiler exposed by those four arrows is
-- now represented by a machine-checked owner.  The only conditional levels below
-- are the irreducible PHYSICAL SOURCE/REPOSITORY instantiations themselves; no
-- extra scalar summability, common-radius, finite-sum Hessian, bare-A Hessian,
-- same-density alias, or covariance theorem is hidden behind the cut.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound103SourceCoordinateWeldExact as R103
import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact as WQR
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as A1
import DASHI.Physics.YangMills.BalabanA2PresentCutFallbackRound120Exact as A2
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as BC1Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as Radius
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Cov

------------------------------------------------------------------------
-- A1 compiled cut
------------------------------------------------------------------------

a1WQRPointwiseAssemblyInterfaceLevel : ProofLevel
a1WQRPointwiseAssemblyInterfaceLevel = WQR.cmp109WQRAssemblyInterfaceLevel

a1FiveChannelEvaluatorDerivedLevel : ProofLevel
a1FiveChannelEvaluatorDerivedLevel = A1.a1FiveChannelEvaluatorDerivedLevel

a1Equation542CompilerLevel : ProofLevel
a1Equation542CompilerLevel = A1.a1ReducedInputsToEquation542CompilerLevel

-- Irreducible physical A1 instantiation: derive the literal W/Q/R symbols from
-- CMP99/CMP98/CMP109 and identify their constrained Gaussian coefficient plus
-- the exact five-channel finite-g term with the physical Eq.(5.1) two-jet.
a1LiteralWQRSourceLevel : ProofLevel
a1LiteralWQRSourceLevel = WQR.cmp109LiteralWQRAssemblyLevel

a1LiteralPhysicalJetSplitLevel : ProofLevel
a1LiteralPhysicalJetSplitLevel = A1.literalA1PhysicalJetGaussianFiveChannelSplitLevel

------------------------------------------------------------------------
-- A2 compiled cut
------------------------------------------------------------------------

a2FullPrefixSubunitCompilerLevel : ProofLevel
a2FullPrefixSubunitCompilerLevel = A2.a2PresentCutFullSubunitLevel

-- `betaMark` is not used as a derivative unless an additional literal theorem
-- identifies it.  The present cut therefore uses the explicit response kernel.
a2OptionalBetaMarkDerivativeLevel : ProofLevel
a2OptionalBetaMarkDerivativeLevel = A2.a2OptionalBetaMarkDerivativeIdentificationLevel

a2LiteralResponseProducerLevel : ProofLevel
a2LiteralResponseProducerLevel = A2.literalA2WardResponseProducerLevel

a2LiteralBetaDifferenceSplitLevel : ProofLevel
a2LiteralBetaDifferenceSplitLevel = A2.literalA2BetaDifferenceDecompositionLevel

------------------------------------------------------------------------
-- BC1 compiled cut
------------------------------------------------------------------------

bc1FiniteDemandsToCommonRadiusLevel : ProofLevel
bc1FiniteDemandsToCommonRadiusLevel = Radius.cmp116FiniteDemandsToCommonRadiusObjectLevel

bc1CanonicalCarrierCompilerLevel : ProofLevel
bc1CanonicalCarrierCompilerLevel = BC1.bc1CanonicalCarrierCompilerLevel

bc1GeneratedActionLocalizedSumLevel : ProofLevel
bc1GeneratedActionLocalizedSumLevel = BC1.bc1GeneratedActionLocalizedSumCompilerLevel

bc1PhysicalCompositeChainRuleLevel : ProofLevel
bc1PhysicalCompositeChainRuleLevel = BC1Chain.bc1PhysicalCompositeChainRuleCompilerLevel

bc1SamePotentialHessianLevel : ProofLevel
bc1SamePotentialHessianLevel = BC1Chain.bc1PhysicalCompositeSamePotentialCompilerLevel

bc1LiteralSourceAndDemandInputsLevel : ProofLevel
bc1LiteralSourceAndDemandInputsLevel = BC1.literalBC1CanonicalPhysicalInputsLevel

bc1LiteralPhysicalCompositeComponentLevel : ProofLevel
bc1LiteralPhysicalCompositeComponentLevel =
  BC1Chain.literalBC1PhysicalCompositeComponentInstantiationLevel

------------------------------------------------------------------------
-- BC2 compiled cut
------------------------------------------------------------------------

bc2CompactGroupSameDensityCompilerLevel : ProofLevel
bc2CompactGroupSameDensityCompilerLevel = BC2.bc2CompactGroupToSameDensityCompilerLevel

bc2StaticMinusCovarianceLevel : ProofLevel
bc2StaticMinusCovarianceLevel = BC2.bc2SamePotentialStaticMinusCovarianceLevel

bc2GradientCovarianceShellCompilerLevel : ProofLevel
bc2GradientCovarianceShellCompilerLevel = Cov.spatialGradientCovarianceWeightedRowCompilerLevel

bc2CompactGroupLogHeatSourceLevel : ProofLevel
bc2CompactGroupLogHeatSourceLevel = BC2.compactGroupLogHeatHessianSourceLevel

bc2LiteralFiniteGaugeHeatSemigroupLevel : ProofLevel
bc2LiteralFiniteGaugeHeatSemigroupLevel =
  BC2.literalFiniteGaugeGroupHeatSemigroupInstantiationLevel

bc2LiteralFirstGradientCovarianceLevel : ProofLevel
bc2LiteralFirstGradientCovarianceLevel =
  Cov.literalCMP116FirstGradientHeatDoobCovarianceInstantiationLevel

------------------------------------------------------------------------
-- Frozen authority
------------------------------------------------------------------------

-- The cut COMPILERS are complete, but the Clay scoreboard cannot move merely
-- because their physical input records have exact types.  The literal source
-- instantiations above must be inhabited without postulates before promotion.
round121FrozenResearchCountStillFour = R103.round103FrozenResearchCountStillFour

rowACompletionRound121Level : ProofLevel
rowACompletionRound121Level = conditional

rowBCompletionRound121Level : ProofLevel
rowBCompletionRound121Level = conditional

rowCCompletionRound121Level : ProofLevel
rowCCompletionRound121Level = conditional

rowDCompletionRound121Level : ProofLevel
rowDCompletionRound121Level = conditional
