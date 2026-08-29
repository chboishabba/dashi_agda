module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound95MasterSyncExact where

------------------------------------------------------------------------
-- ROUND95: MASTER-FIRST HIGHEST-ALPHA FRONTIER
--
-- This root starts from current master, not the old long-lived Round61 PR
-- branch.  Master already contains the stronger Row-A gate composition and
-- cubic-telescope shooting sensitivity algebra.  Round95 sharpens that further:
-- BOTH Row-A numerical gates follow from one source smallness inequality
--
--                     (C + L) gamma < b_-.
--
-- Moreover gamma is no longer an existential tuning parameter.  Given a
-- positive floor b_- and finite nonnegative C,L, choose canonically
--
--                 gamma = b_- / (2 (C + L + 1)).
--
-- Exact rational arithmetic proves this gamma is positive and pays the combined
-- gate.  Thus the remaining A-side scalar work is source identification of the
-- positive floor and finite source constants on the literal same trajectory.
--
-- Round95 also advances B and the B->C temporal fusion:
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
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as ACanonical
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as BSum
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact as BC
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToPolchinskiIntegralDebtExact as BCIntegral

------------------------------------------------------------------------
-- A: two numerical gates collapse to one canonical small-coupling choice
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

-- Physical A seam after Round95: derive on the literal source trajectory
--   * b_- > 0,
--   * finite C >= 0,
--   * finite L >= 0,
-- and identify the source tube with width no larger than the canonical gamma.
-- The existence and arithmetic of a sufficiently-small coupling cap are now
-- theorem-owned rather than a second physical estimate.
rowALiteralFiniteSourceConstantsRound95Level : ProofLevel
rowALiteralFiniteSourceConstantsRound95Level = conditional

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
