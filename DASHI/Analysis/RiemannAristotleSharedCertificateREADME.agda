module DASHI.Analysis.RiemannAristotleSharedCertificateREADME where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Import-only aggregation/navigation root for the Aristotle / RH return lane.
--
-- The current returned state includes the exact two-zero / three-taper theorem,
-- the explicit finite-near/far decomposition, the optimized gap-split no-go,
-- the §37 quarter-period/density reconciliation, and the §38 actual-zeta upper
-- local-count instance. The existing gap-split, adaptive-window, quarter-period
-- and canonical RH schedulers consume those returns directly, so this is one
-- welded dependency graph rather than parallel status ledgers.
--
-- The Alpöge--Furman >2/3 simple/on-critical-line theorem is audited against
-- the live local-clustering consumer: its global population summary does not
-- descend directly to the selected target-local gap pattern.
--
-- A further carrier audit separates transverse alpha = Re(rho)-1/2 from the
-- target-relative ordinate gap delta = Im(rho)-t. The existing Hermitian
-- transverse-moment lane is therefore NOT a direct donor for low-gap clustering.
-- The correct in-repo carrier is the targetRelativeGap coordinate of the
-- PoleNearPhaseStatistic lane. The local second-moment compiler is welded to the
-- existing ActualSelectedPoleNearProducer, so target, multiplicity and
-- nearOffFinset cannot silently change.
--
-- Genuine zeta clustering, the selected-window delta-moment producer,
-- same-object finite-near evaluation, Gamma precision, low-ordinate/global
-- coverage and RH remain open.
------------------------------------------------------------------------

import DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact
import DASHI.Analysis.CertifiedFiniteCarrierReindexExact
import DASHI.Analysis.RiemannAristotleSharedCertificateReturnExact
import DASHI.Analysis.RiemannAristotleSharedCertificateReturnRegression
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnRegression
import DASHI.Analysis.ExactSelectedEliminationFarTailCompilerExact
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact
import DASHI.Analysis.RiemannG2TransverseVsOrdinateMomentNonDescentExact
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact
import DASHI.Analysis.RiemannG2SelectedTargetLocalMomentSameObjectExact
import DASHI.Analysis.RiemannG2AdaptiveJLambdaConstantWindowExact
import DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact
import DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact
import DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact
import DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact
import DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact
import DASHI.Analysis.RiemannAristotleCurrentFrontierRegression
