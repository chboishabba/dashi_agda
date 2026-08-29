module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound95MasterSyncExact where

------------------------------------------------------------------------
-- ROUND95: MASTER-FIRST HIGHEST-ALPHA FRONTIER
--
-- This root starts from current master, not the old long-lived Round61 PR
-- branch.  Master already contains the stronger Row-A gate composition and
-- cubic-telescope shooting sensitivity algebra.  Round95 sharpens that further:
-- on a source tube with width <= gamma, BOTH Row-A numerical gates follow from
--
--                     (C + L) gamma < b_-.
--
-- It also advances B and the B->C temporal fusion:
--
--   differentiated activity A a^n
--   × shell entropy B e^n
--       -> E_n <= AB (ae)^n
--       -> uniform marked-shell cap;
--
-- and if the SAME marked shell dominates the same-density curvature shell,
-- with ae <= 17/32,
--
--       eta_n <= E_n
--       -> finite total curvature debt.
--
-- If the actual Polchinski/Heat-Doob shell integral also obeys I_n <= eta_n,
-- the existing integral compiler gives the continuous-time debt bound.  Thus
-- Row C temporal summability can be paid by the same physical estimate that
-- closes Row B.  Spatial influence/clustering remains separate.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact as R87
import DASHI.Physics.YangMills.BalabanYM4RowAGateCompositionExact as A
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as AShoot
import DASHI.Physics.YangMills.BalabanYM4RowACombinedSmallCouplingGateExact as AOne
import DASHI.Physics.YangMills.BalabanYM4RowACombinedGateCompositionExact as ACompose
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as BSum
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact as BC
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToPolchinskiIntegralDebtExact as BCIntegral

------------------------------------------------------------------------
-- A: two numerical gates collapse to one source smallness inequality
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

-- Physical A seam after Round95: identify the literal positive floor b_- and
-- finite interaction/derivative constants C,L on one source tube, arrange
-- tubeWidth <= gamma, and prove the single strict inequality
--
--                         (C + L) gamma < b_-.
--
-- Positivity and shooting contraction then share the same small-coupling choice.
rowALiteralOneGateInstantiationRound95Level : ProofLevel
rowALiteralOneGateInstantiationRound95Level = conditional

------------------------------------------------------------------------
-- B: source activity × entropy is now the only geometric-shell producer
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

rowBLiteralCMP116ActivityEntropyRound95Level : ProofLevel
rowBLiteralCMP116ActivityEntropyRound95Level = conditional

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

rowBCSameDensityPhysicalDominationRound95Level : ProofLevel
rowBCSameDensityPhysicalDominationRound95Level = conditional

------------------------------------------------------------------------
-- Frozen four-row authority remains unchanged
------------------------------------------------------------------------

round95FrozenResearchCountStillFour = R87.round87ShortestClayAnalyticCount

rowACompletionRound95Level : ProofLevel
rowACompletionRound95Level = conditional

rowBCompletionRound95Level : ProofLevel
rowBCompletionRound95Level = conditional

rowCCompletionRound95Level : ProofLevel
rowCCompletionRound95Level = conditional

rowDCompletionRound95Level : ProofLevel
rowDCompletionRound95Level = conditional
