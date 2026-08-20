module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound54G1G2BetaCompleteDensityValidation where

------------------------------------------------------------------------
-- ROUND 54 FOCUSED VALIDATION ROOT
--
-- Required fronts of this tranche:
--
-- G1
--   literal CMP109 centre convention
--     -> J_+(Y) Ad_{exp Y} = J_-(Y)
--     -> source-radius inverse-dexp quarter defect
--     -> source-norm 4/3 reopening.
--
-- G2
--   physical selected-singleton core
--     + uniform cancellation-preserving interval enclosure on the certified
--       minimizer region
--     -> joint residual bound on the SAME canonical residual family
--     -> actual selected singleton witness.
--
-- beta / CMP119-CMP122
--   literal plaquette beta_Z + beta_int
--     -> SU(2) Gaussian 11/12 log-step lower
--     -> quartic interaction half-gap
--     -> repository FiniteLatticeBetaSplit
--     -> terminal inverse-square small-coupling history
--     -> beta-driven CMP122 effective-density flow
--     -> canonical YM4RGState with the SAME running coupling.
--
-- This root intentionally does not import the later continuum/OS reconstruction
-- programme.  The full physical numerical certificates remain fail-closed:
-- selected-minimizer interval evaluation, finite Brillouin/log enclosure,
-- quartic beta remainder, and literal Section-2 scalar-coordinate extraction.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound53LiteralFederbushCouplingValidation as R53
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushConventionCancellationExact as G1
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogSourceOperatorDefectExact as G1Norm
import DASHI.Physics.YangMills.BalabanCMP109SourceNormQuarterReopeningExact as G1Open
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerJointProducerExact as G2
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as BetaStep
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as BetaLiteral
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as BetaGaussian
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaHistoryExact as BetaHistory
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as SourceFlow
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact as Canonical

literalFederbushConventionCancellationLevel =
  G1.cmp109PhysicalFederbushConventionCancellationLevel

literalFederbushCentreActionLevel =
  G1.cmp109PhysicalFederbushPrintedCentreActionLevel

sourceOperatorInverseDexpQuarterLevel =
  G1Norm.cmp109SourceOperatorInverseDexpQuarterLevel

sourceNormFourThirdsReopeningLevel =
  G1Open.cmp109SourceNormQuarterReopeningLevel

uniformSelectedMinimizerJointProducerLevel =
  G2.p33UniformSelectedMinimizerJointProducerLevel

finiteLatticeBetaHalfGapLevel =
  BetaStep.ym4FiniteLatticeBetaHalfGapLevel

literalPlaquetteBetaSplitLevel =
  BetaLiteral.ym4LiteralPlaquetteBetaSplitLevel

literalPlaquetteFiniteBetaEstimateLevel =
  BetaLiteral.ym4LiteralPlaquetteFiniteBetaEstimateLevel

su2GaussianFiniteLatticeLowerLevel =
  BetaGaussian.ym4SU2GaussianFiniteLatticeLowerLevel

finiteLatticeBetaHistoryAssemblyLevel =
  BetaHistory.ym4FiniteLatticeBetaHistoryAssemblyLevel

betaDrivenCMP122FlowLevel =
  SourceFlow.balabanBetaDrivenSourceFlowLevel

betaHistoryIsLiteralCMP122CouplingLevel =
  SourceFlow.balabanBetaHistoryIsLiteralCMP122CouplingLevel

betaDrivenCanonicalYM4StateLevel =
  Canonical.balabanBetaDrivenCanonicalStateLevel

betaDrivenCMP122RepositoryRegionLevel =
  Canonical.balabanBetaDrivenCMP122ToRepositoryRegionLevel
