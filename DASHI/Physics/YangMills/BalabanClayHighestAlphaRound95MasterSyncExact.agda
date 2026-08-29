module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound95MasterSyncExact where

------------------------------------------------------------------------
-- ROUND95--97: MASTER-FIRST BIDIRECTIONAL HIGHEST-ALPHA FRONTIER
--
-- Proof search is now explicitly bidirectional:
--
--   backward: inspect the literal A/B/C/D completion consumers and ask for the
--             weakest quantitative object that actually closes the next edge;
--   forward:  start from the strongest source-native CMP98/99/109/116 producers
--             already present and push them into exactly that consumer shape.
--
-- ROW A
-- -----
-- * normalized-interaction Cauchy data gives C and L_local;
-- * the Ward patch fixes the Gaussian arithmetic floor at 1/8388608 pending
--   literal same-object identification;
-- * irrelevant/polymer history is separated from the marginal running coupling;
-- * contractive irrelevant memory + a Lipschitz beta projection + initial-input
--   response D0 <= S |delta u| gives cutoff-uniform history sensitivity 2 L S;
-- * if S <= S0 gamma then q_history <= H gamma, H = 2 L S0;
-- * direct + history shooting therefore closes under the single scalar gate
--
--       (C + L_local + b H) gamma < b,
--
--   with gamma chosen canonically downstream.
--
-- Thus the live A sensitivity leaf is source-native: prove the initial
-- irrelevant/polymer response to the inverse-square shooting input is O(gamma)
-- on the SAME uniform analytic tube, while completing the Ward-floor and
-- normalized-interaction same-object welds.
--
-- ROW B
-- -----
-- The shared CMP116 marked analytic carrier itself gives r=1/2 geometric decay
-- for beta-history, physical Hessian and composite marks.  Geometric shell
-- summation is therefore downstream after literal marked-coordinate/radius
-- identification.  Stress can reuse the composite mark after source identity.
--
-- ROW B -> C, TEMPORAL
-- --------------------
-- Since 1/2 <= 17/32, the same physical Hessian mark pays the temporal
-- curvature-debt envelope whenever the SAME-density Heat/Doob negative Hessian
-- shell is pointwise dominated by that mark.
--
-- ROW B -> C, SPATIAL (ROUND97 BIDI FUSION)
-- -------------------------------------------
-- Row C finite-speed propagation does not need a second all-depth locality
-- theorem.  Backwards inspection shows it needs one finite nonnegative influence
-- majorant M with a uniform row mass.  Forward CMP116 control already supplies
-- the exponentially weighted Hessian row constant C_H.  Round97 therefore asks
-- only for the SAME derivative-generator row comparison
--
--                   sum_y M(x,y) <= C_H.
--
-- A new exact compiler proves nonnegative entries imply nonnegative every matrix
-- power, then the existing row-mass induction gives
--
--                   row(M^n) <= C_H^n.
--
-- Thus positivity of all Dyson powers and their row bounds are no longer
-- physical inputs.  The remaining spatial seam is same-density generator-to-
-- marked-Hessian identification plus the already-declared stochastic covariance
-- representation/relaxation inputs.
--
-- The frozen four-row count remains four.  A row decrements only on an inhabited
-- literal physical completion predicate or a theorem eliminating that whole row.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact as R87
import DASHI.Physics.YangMills.BalabanYM4RowAGateCompositionExact as A
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as AShoot
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

import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as BSum
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as BShared

import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact as BC
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToPolchinskiIntegralDebtExact as BCIntegral
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToCurvatureDebtExact as BCHessian
import DASHI.Physics.YangMills.BalabanFiniteInfluenceNonnegativePowersExact as CPositive
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToFiniteInfluenceExact as CInfluence

------------------------------------------------------------------------
-- A: local source constants + explicit Ward floor + isolated history response
------------------------------------------------------------------------

rowACubicShootingSensitivityAlgebraRound95Level : ProofLevel
rowACubicShootingSensitivityAlgebraRound95Level = machineChecked

rowATwoNumericalGateCompositionRound95Level : ProofLevel
rowATwoNumericalGateCompositionRound95Level = machineChecked

rowACombinedSmallnessToSignGateRound95Level : ProofLevel
rowACombinedSmallnessToSignGateRound95Level =
  AOne.rowACombinedSmallnessToSignGateLevel

rowACombinedSmallnessToShootingGateRound95Level : ProofLevel
rowACombinedSmallnessToShootingGateRound95Level =
  AOne.rowACombinedSmallnessToShootingGateLevel

rowAOneSmallnessGateCompositionRound95Level : ProofLevel
rowAOneSmallnessGateCompositionRound95Level =
  ACompose.rowAOneSmallnessGateCompositionLevel

rowACanonicalGammaPositiveRound95Level : ProofLevel
rowACanonicalGammaPositiveRound95Level =
  ACanonical.rowACanonicalGammaPositiveLevel

rowACanonicalGammaPaysCombinedGateRound95Level : ProofLevel
rowACanonicalGammaPaysCombinedGateRound95Level =
  ACanonical.rowACanonicalGammaPaysCombinedGateLevel

rowALocalCauchyConstantsToCanonicalGateRound96Level : ProofLevel
rowALocalCauchyConstantsToCanonicalGateRound96Level =
  ACauchy.rowACauchyLocalConstantsToCanonicalGammaLevel

rowAWardFloorArithmeticRound96Level : ProofLevel
rowAWardFloorArithmeticRound96Level =
  AWard.wardGaussianFloorArithmeticLevel

rowAIrrelevantHistoryInputSensitivityRound96Level : ProofLevel
rowAIrrelevantHistoryInputSensitivityRound96Level =
  AHistory.rowAIrrelevantHistoryInputSensitivityLevel

rowAInitialResponseToHistoryLinearCouplingRound96Level : ProofLevel
rowAInitialResponseToHistoryLinearCouplingRound96Level =
  AHistoryLinear.rowAInitialResponseToHistoryLinearCouplingLevel

rowAAugmentedDirectHistoryShootingRound96Level : ProofLevel
rowAAugmentedDirectHistoryShootingRound96Level =
  AAugmented.rowAAugmentedShootingSubunitLevel

rowAHistorySuppressedCombinedGateRound96Level : ProofLevel
rowAHistorySuppressedCombinedGateRound96Level =
  AHistoryGate.rowAHistorySuppressedAugmentedGateLevel

rowAHistoryAugmentedCanonicalChoiceRound96Level : ProofLevel
rowAHistoryAugmentedCanonicalChoiceRound96Level =
  AHistoryChoice.rowAAugmentedCanonicalChoiceLevel

rowALiteralFiniteSourceConstantsRound97Level : ProofLevel
rowALiteralFiniteSourceConstantsRound97Level = conditional

------------------------------------------------------------------------
-- B: shared CMP116 marked control already gives geometric r = 1/2 shells
------------------------------------------------------------------------

rowBActivityEntropyProductRound95Level : ProofLevel
rowBActivityEntropyProductRound95Level =
  B.rowBActivityEntropyProductAlgebraLevel

rowBActivityEntropyToGeometricShellRound95Level : ProofLevel
rowBActivityEntropyToGeometricShellRound95Level =
  B.rowBActivityEntropyToGeometricShellLevel

rowBUniformShellSummationRound95Level : ProofLevel
rowBUniformShellSummationRound95Level =
  B.rowBActivityEntropyUniformSummationLevel

rowBSharedMarkedControlToGeometricHalfRound96Level : ProofLevel
rowBSharedMarkedControlToGeometricHalfRound96Level =
  BShared.sharedMarkedControlToGeometricHalfLevel

rowBHessianGeometricHalfRound96Level : ProofLevel
rowBHessianGeometricHalfRound96Level =
  BShared.sharedHessianGeometricShellLevel

rowBCompositeGeometricHalfRound96Level : ProofLevel
rowBCompositeGeometricHalfRound96Level =
  BShared.sharedCompositeGeometricShellLevel

rowBLiteralCMP116SharedMarkedInstantiationRound97Level : ProofLevel
rowBLiteralCMP116SharedMarkedInstantiationRound97Level = conditional

------------------------------------------------------------------------
-- B -> C temporal fusion
------------------------------------------------------------------------

rowBCMarkedShellToCurvatureCarrierRound95Level : ProofLevel
rowBCMarkedShellToCurvatureCarrierRound95Level =
  BC.rowBCMarkedShellToCurvatureCarrierLevel

rowBCMarkedShellToUniformCurvatureDebtRound95Level : ProofLevel
rowBCMarkedShellToUniformCurvatureDebtRound95Level =
  BC.rowBCMarkedShellToUniformCurvatureDebtLevel

rowBCMarkedShellToIntegratedDebtRound95Level : ProofLevel
rowBCMarkedShellToIntegratedDebtRound95Level =
  BCIntegral.rowBCMarkedShellToUniformIntegratedCurvatureDebtLevel

rowBSharedHessianPaysCurvatureDebtRound96Level : ProofLevel
rowBSharedHessianPaysCurvatureDebtRound96Level =
  BCHessian.sharedHessianToUniformCurvatureDebtLevel

rowBCSameDensityTemporalDominationRound97Level : ProofLevel
rowBCSameDensityTemporalDominationRound97Level = conditional

------------------------------------------------------------------------
-- B -> C spatial fusion: one Hessian row -> all finite influence powers
------------------------------------------------------------------------

rowCInfluencePowerPositivityRound97Level : ProofLevel
rowCInfluencePowerPositivityRound97Level =
  CPositive.finiteInfluencePowerPositivityLevel

rowCInfluencePowerRowMassRound97Level : ProofLevel
rowCInfluencePowerRowMassRound97Level =
  CPositive.finiteInfluencePowerRowMassFromSingleMajorantLevel

rowBSharedHessianToFiniteInfluenceCarrierRound97Level : ProofLevel
rowBSharedHessianToFiniteInfluenceCarrierRound97Level =
  CInfluence.sharedMarkedHessianToFiniteInfluenceCarrierLevel

rowBSharedHessianToAllInfluencePowerRowsRound97Level : ProofLevel
rowBSharedHessianToAllInfluencePowerRowsRound97Level =
  CInfluence.sharedMarkedHessianToAllInfluencePowerRowsLevel

-- Current spatial physical seam after the BIDI fusion:
-- identify the literal absolute derivative generator of the SAME compact-group
-- Heat/Doob dynamics with the finite majorant and prove its one-row sum is below
-- the already-required shared CMP116 hessian constant.  The all-power Dyson row
-- bounds are downstream exact finite algebra.  The stochastic covariance split
-- and same-density temporal relaxation remain the other declared inputs to the
-- existing spatial-clustering compiler.
rowBCSameDensityGeneratorRowIdentificationRound97Level : ProofLevel
rowBCSameDensityGeneratorRowIdentificationRound97Level = conditional

------------------------------------------------------------------------
-- Frozen four-row authority remains unchanged
------------------------------------------------------------------------

round97FrozenResearchCountStillFour = R87.round87ShortestClayAnalyticCount

rowACompletionRound97Level : ProofLevel
rowACompletionRound97Level = conditional

rowBCompletionRound97Level : ProofLevel
rowBCompletionRound97Level = conditional

rowCCompletionRound97Level : ProofLevel
rowCCompletionRound97Level = conditional

rowDCompletionRound97Level : ProofLevel
rowDCompletionRound97Level = conditional
