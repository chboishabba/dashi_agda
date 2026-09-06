module DASHI.Analysis.RiemannAristotleSharedCertificateREADME where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Import-only aggregation/navigation root for the Aristotle / RH return lane.
--
-- The current returned state includes the exact two-zero / three-taper theorem,
-- the explicit finite-near/far decomposition, the optimized gap-split no-go,
-- the §37 quarter-period/density reconciliation, and the §38 actual-zeta upper
-- local-count instance.  The existing gap-split, adaptive-window, quarter-period
-- scheduler and highest-alpha owners consume those returns directly, so this is
-- one welded dependency graph rather than parallel status ledgers.
--
-- Genuine zeta clustering and long-window lower density remain open.
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
import DASHI.Analysis.RiemannG2AdaptiveJLambdaConstantWindowExact
import DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact
import DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact
import DASHI.Analysis.RiemannAristotleNearCoreDensityReturnRegression
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact
import DASHI.Analysis.RiemannAristotleCurrentFrontierRegression
