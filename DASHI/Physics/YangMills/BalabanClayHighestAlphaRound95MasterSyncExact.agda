module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound95MasterSyncExact where

------------------------------------------------------------------------
-- ROUND95--99: MASTER-FIRST BIDIRECTIONAL HIGHEST-ALPHA FRONTIER
--
-- Proof search is explicitly bidirectional:
--
--   backward: inspect the literal A/B/C/D completion consumers and ask for the
--             weakest quantitative object that actually closes the next edge;
--   forward:  start from the strongest source-native CMP98/99/109/116 producers
--             already present and push them into exactly that consumer shape.
--
-- ROW A
-- -----
-- Local data already provide the Ward candidate floor b, interaction debt C and
-- direct current-coupling derivative L_local.  Marginal coupling is never given
-- fake exponential forgetting.
--
-- Round98 adds the response-kernel route matching the parallel Lean producer:
--
--       r_(n+1) <= R s_n + (1/2) r_n
--         -> sum r_n <= 2 R sum s_n.
--
-- If direct history injection is quartic,
--
--       s_j <= D g_j^4,
--
-- the SAME inverse-square drift gives
--
--       sum s_j <= D gamma (2 gamma_tube / b_*).
--
-- Multiplying by the shooting margin cancels b_*^{-1}, leaving at most
-- 4 R D gamma^2.  For gamma<=1 the complete direct+history gate therefore follows
-- from the single linearized inequality
--
--       (C + L_local + 4 R D) gamma < b.
--
-- The canonical rational choice is reused with effective derivative
-- L_local+4RD.  With the fixed Ward floor b=1/8388608, gamma<=1/2 follows by
-- exact arithmetic.  `WardQuarticResponseProducer` now packages the whole
-- numerical path: once the literal trajectory supplies mixed-Cauchy data, the
-- response kernel, quartic injection and recurrence/cap identities, the strict
-- shooting gate is constructed automatically.
--
-- ROW B
-- -----
-- The shared CMP116 marked analytic carrier gives r=1/2 geometric decay for
-- beta-history, physical Hessian and composite marks.  Geometric summation is
-- downstream after literal marked-coordinate/radius identification.
--
-- ROW B -> C, TEMPORAL
-- --------------------
-- Since 1/2 <= 17/32, the same physical Hessian mark pays the temporal curvature
-- debt whenever the SAME-density Heat/Doob negative Hessian shell is pointwise
-- dominated by that mark.
--
-- ROW B -> C, SPATIAL (ROUND99)
-- --------------------------------
-- The earlier unweighted row reduction was useful but discarded information.
-- CMP116 actually gives an exponentially weighted Hessian row.  Round99 keeps
-- that weight all the way through the finite Dyson algebra.
--
-- For a finite nonnegative generator M and a submultiplicative weight w,
--
--       sum_y w(x,y) M(x,y) <= C_H
--
-- now implies for every positive matrix power
--
--       sum_y w(x,y) M^n(x,y) <= C_H^n.
--
-- The weight used by the existing Hessian lane is w=(3/2)^distance.  Exact Agda
-- arithmetic now proves ordinary Nat triangle inequality implies w>=1 and
-- w(x,z)<=w(x,y)w(y,z).  Therefore the preferred physical C-spatial leaf is only
-- the SAME-density, SAME-metric row comparison between the absolute covariant
-- derivative generator and the already-required CMP116 Hessian mark.  Weight
-- algebra, power positivity and all-power propagation are theorem-owned.
--
-- The frozen four-row count remains four.  A row decrements only on an inhabited
-- literal physical completion predicate or a theorem eliminating that whole row.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact as R87
import DASHI.Physics.YangMills.BalabanYM4RowACombinedSmallCouplingGateExact as AOne
import DASHI.Physics.YangMills.BalabanYM4RowACombinedGateCompositionExact as ACompose
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as ACanonical
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as ACauchy
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as AWard
import DASHI.Physics.YangMills.BalabanYM4RowAIrrelevantHistoryInputSensitivityExact as AHistory
import DASHI.Physics.YangMills.BalabanYM4RowAIrrelevantHistoryLinearCouplingExact as AHistoryLinear
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as AAugmented
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalHistoryGateExact as AHistoryGate
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalChoiceExact as AHistoryChoice
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as AResponse
import DASHI.Physics.YangMills.BalabanYM4FiniteBetaResponseKernelBudgetExact as AFiniteResponse
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as AQuarticBudget
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact as AQuarticGate
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as AQuarticChoice
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseCanonicalChoiceExact as AWardQuartic
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as AProducer

import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as BShared

import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact as BC
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToPolchinskiIntegralDebtExact as BCIntegral
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToCurvatureDebtExact as BCHessian
import DASHI.Physics.YangMills.BalabanFiniteInfluenceNonnegativePowersExact as CPositive
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToFiniteInfluenceExact as CInfluence
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as CWeighted
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as CMetric
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as CWeightedBridge
import DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact as CMetricBridge

------------------------------------------------------------------------
-- A: direct/history shooting and response-kernel collapse
------------------------------------------------------------------------

rowACombinedSmallnessToSignGateRound95Level : ProofLevel
rowACombinedSmallnessToSignGateRound95Level = AOne.rowACombinedSmallnessToSignGateLevel

rowAOneSmallnessGateCompositionRound95Level : ProofLevel
rowAOneSmallnessGateCompositionRound95Level = ACompose.rowAOneSmallnessGateCompositionLevel

rowACanonicalGammaPositiveRound95Level : ProofLevel
rowACanonicalGammaPositiveRound95Level = ACanonical.rowACanonicalGammaPositiveLevel

rowALocalCauchyConstantsToCanonicalGateRound96Level : ProofLevel
rowALocalCauchyConstantsToCanonicalGateRound96Level = ACauchy.rowACauchyLocalConstantsToCanonicalGammaLevel

rowAWardFloorArithmeticRound96Level : ProofLevel
rowAWardFloorArithmeticRound96Level = AWard.wardGaussianFloorArithmeticLevel

rowAIrrelevantHistoryInputSensitivityRound96Level : ProofLevel
rowAIrrelevantHistoryInputSensitivityRound96Level = AHistory.rowAIrrelevantHistoryInputSensitivityLevel

rowAInitialResponseToHistoryLinearCouplingRound96Level : ProofLevel
rowAInitialResponseToHistoryLinearCouplingRound96Level = AHistoryLinear.rowAInitialResponseToHistoryLinearCouplingLevel

rowAAugmentedDirectHistoryShootingRound96Level : ProofLevel
rowAAugmentedDirectHistoryShootingRound96Level = AAugmented.rowAAugmentedShootingSubunitLevel

rowAHistorySuppressedCombinedGateRound96Level : ProofLevel
rowAHistorySuppressedCombinedGateRound96Level = AHistoryGate.rowAHistorySuppressedAugmentedGateLevel

rowAHistoryAugmentedCanonicalChoiceRound96Level : ProofLevel
rowAHistoryAugmentedCanonicalChoiceRound96Level = AHistoryChoice.rowAAugmentedCanonicalChoiceLevel

rowAResponseKernelPotentialRound98Level : ProofLevel
rowAResponseKernelPotentialRound98Level = AResponse.betaResponseKernelPotentialLevel

rowAResponseKernelFiniteBudgetRound98Level : ProofLevel
rowAResponseKernelFiniteBudgetRound98Level = AFiniteResponse.finiteBetaResponseKernelBudgetLevel

rowAQuarticInjectionToFiniteBudgetRound98Level : ProofLevel
rowAQuarticInjectionToFiniteBudgetRound98Level = AQuarticBudget.quarticSourceSensitivityToFiniteBudgetLevel

rowAQuarticResponseMarginCancellationRound98Level : ProofLevel
rowAQuarticResponseMarginCancellationRound98Level = AQuarticGate.rowAQuarticResponseMarginCancellationLevel

rowAQuarticResponseSingleGateRound98Level : ProofLevel
rowAQuarticResponseSingleGateRound98Level = AQuarticGate.rowAQuarticResponseSingleLinearGateLevel

rowAQuarticResponseCanonicalChoiceRound98Level : ProofLevel
rowAQuarticResponseCanonicalChoiceRound98Level = AQuarticChoice.rowAQuarticResponseCanonicalChoiceLevel

rowAWardQuarticCanonicalChoiceRound99Level : ProofLevel
rowAWardQuarticCanonicalChoiceRound99Level = AWardQuartic.wardQuarticResponseCanonicalChoiceLevel

rowAWardQuarticProducerToShootingRound99Level : ProofLevel
rowAWardQuarticProducerToShootingRound99Level = AProducer.rowAWardQuarticResponseProducerToShootingLevel

-- Current physical A seam after Round99:
--  1. literal CMP109/CMP99 Ward patch -> mixed beta jet same-object floor;
--  2. literal normalized interaction mixed-Cauchy package;
--  3. literal irrelevant/polymer response kernel;
--  4. literal direct history injection <= D g_j^4 (or the older O(gamma)
--     initial-response route if source-native and weaker);
--  5. exact recurrence/cap identification for the generated trajectory.
-- The finite constants, summation, q<1 margin and canonical cap are downstream.
rowALiteralSourceInstantiationRound99Level : ProofLevel
rowALiteralSourceInstantiationRound99Level = conditional

------------------------------------------------------------------------
-- B: shared CMP116 marked control already gives geometric r = 1/2 shells
------------------------------------------------------------------------

rowBActivityEntropyProductRound95Level : ProofLevel
rowBActivityEntropyProductRound95Level = B.rowBActivityEntropyProductAlgebraLevel

rowBActivityEntropyToGeometricShellRound95Level : ProofLevel
rowBActivityEntropyToGeometricShellRound95Level = B.rowBActivityEntropyToGeometricShellLevel

rowBUniformShellSummationRound95Level : ProofLevel
rowBUniformShellSummationRound95Level = B.rowBActivityEntropyUniformSummationLevel

rowBSharedMarkedControlToGeometricHalfRound96Level : ProofLevel
rowBSharedMarkedControlToGeometricHalfRound96Level = BShared.sharedMarkedControlToGeometricHalfLevel

rowBHessianGeometricHalfRound96Level : ProofLevel
rowBHessianGeometricHalfRound96Level = BShared.sharedHessianGeometricShellLevel

rowBCompositeGeometricHalfRound96Level : ProofLevel
rowBCompositeGeometricHalfRound96Level = BShared.sharedCompositeGeometricShellLevel

rowBLiteralCMP116SharedMarkedInstantiationRound99Level : ProofLevel
rowBLiteralCMP116SharedMarkedInstantiationRound99Level = conditional

------------------------------------------------------------------------
-- B -> C temporal fusion
------------------------------------------------------------------------

rowBCMarkedShellToCurvatureCarrierRound95Level : ProofLevel
rowBCMarkedShellToCurvatureCarrierRound95Level = BC.rowBCMarkedShellToCurvatureCarrierLevel

rowBCMarkedShellToUniformCurvatureDebtRound95Level : ProofLevel
rowBCMarkedShellToUniformCurvatureDebtRound95Level = BC.rowBCMarkedShellToUniformCurvatureDebtLevel

rowBCMarkedShellToIntegratedDebtRound95Level : ProofLevel
rowBCMarkedShellToIntegratedDebtRound95Level = BCIntegral.rowBCMarkedShellToUniformIntegratedCurvatureDebtLevel

rowBSharedHessianPaysCurvatureDebtRound96Level : ProofLevel
rowBSharedHessianPaysCurvatureDebtRound96Level = BCHessian.sharedHessianToUniformCurvatureDebtLevel

rowBCSameDensityTemporalDominationRound99Level : ProofLevel
rowBCSameDensityTemporalDominationRound99Level = conditional

------------------------------------------------------------------------
-- B -> C spatial fusion: retain metric exponential weight through all powers
------------------------------------------------------------------------

rowCInfluencePowerPositivityRound97Level : ProofLevel
rowCInfluencePowerPositivityRound97Level = CPositive.finiteInfluencePowerPositivityLevel

rowCInfluencePowerRowMassRound97Level : ProofLevel
rowCInfluencePowerRowMassRound97Level = CPositive.finiteInfluencePowerRowMassFromSingleMajorantLevel

rowBSharedHessianToFiniteInfluenceCarrierRound97Level : ProofLevel
rowBSharedHessianToFiniteInfluenceCarrierRound97Level = CInfluence.sharedMarkedHessianToFiniteInfluenceCarrierLevel

rowCWeightedInfluenceAllPowerRowsRound99Level : ProofLevel
rowCWeightedInfluenceAllPowerRowsRound99Level = CWeighted.finiteWeightedInfluenceAllPowerRowLevel

rowCThreeHalvesMetricWeightRound99Level : ProofLevel
rowCThreeHalvesMetricWeightRound99Level = CMetric.threeHalvesMetricWeightSubmultiplicativeLevel

rowBSharedHessianToWeightedInfluenceRound99Level : ProofLevel
rowBSharedHessianToWeightedInfluenceRound99Level = CWeightedBridge.sharedMarkedHessianToWeightedAllPowerRowsLevel

rowBSharedMetricHessianToAllWeightedRowsRound99Level : ProofLevel
rowBSharedMetricHessianToAllWeightedRowsRound99Level = CMetricBridge.sharedMarkedMetricToAllWeightedPowerRowsLevel

-- Preferred C-spatial physical seam:
-- identify the literal same-density absolute derivative generator and the
-- CMP116 Hessian mark on the actual integer lattice/block metric, and prove the
-- single weighted row inequality.  Metric-weight algebra and all finite Dyson
-- power propagation are theorem-owned.  Same-density temporal relaxation and
-- the covariance representation are the remaining stochastic ingredients.
rowBCSameDensityWeightedGeneratorRowRound99Level : ProofLevel
rowBCSameDensityWeightedGeneratorRowRound99Level = conditional

------------------------------------------------------------------------
-- Frozen four-row authority remains unchanged
------------------------------------------------------------------------

round99FrozenResearchCountStillFour = R87.round87ShortestClayAnalyticCount

rowACompletionRound99Level : ProofLevel
rowACompletionRound99Level = conditional

rowBCompletionRound99Level : ProofLevel
rowBCompletionRound99Level = conditional

rowCCompletionRound99Level : ProofLevel
rowCCompletionRound99Level = conditional

rowDCompletionRound99Level : ProofLevel
rowDCompletionRound99Level = conditional
