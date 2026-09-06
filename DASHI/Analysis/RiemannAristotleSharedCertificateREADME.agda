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
-- The Alpoge--Furman >2/3 simple/on-critical-line theorem is audited against the
-- live local-clustering consumer: its global population summary does not descend
-- directly to the selected target-local gap pattern.
--
-- A further carrier audit separates transverse alpha = Re(rho)-1/2 from the
-- target-relative ordinate gap delta = Im(rho)-t. The existing Hermitian
-- transverse-moment lane is therefore NOT a direct donor for low-gap clustering.
--
-- The existing DirectFinitePoleNearProducer is now the canonical concrete
-- target-gap/phase carrier: PoleNearPhaseStatistic compiles from it, rather than
-- requiring another ZeroIndex/phase object. The direct producer already carries
-- nearIndex, multiplicity, targetRelativeGap and a signed approximant/error
-- receipt. It must subsequently be welded to the existing
-- ActualSelectedPoleNearProducer. That same-object weld then fans out to both
-- the selected delta^2 moment and the selected finite-near consumer attachment.
--
-- Dependency order:
--
--   DirectFinitePoleNearProducer + ActualSelectedPoleNearProducer
--      -> SelectedDirectFiniteWeld
--          -> selected delta^2 moment -> clustering
--          -> selected finite-near budget transport
--
-- Genuine zeta clustering, both producer instantiations, their same-object weld,
-- the selected-window delta-moment estimate, consumer-sufficient finite-near
-- budget, Gamma precision, low-ordinate/global coverage and RH remain open.
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
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact
import DASHI.Analysis.RiemannG2AdaptiveJLambdaConstantWindowExact
import DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact
import DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact
import DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact
import DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact
import DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact
import DASHI.Analysis.RiemannAristotleCurrentFrontierRegression
