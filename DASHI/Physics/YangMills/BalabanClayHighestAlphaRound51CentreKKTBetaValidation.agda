module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound51CentreKKTBetaValidation where

------------------------------------------------------------------------
-- Focused Round-51 validation root.
--
-- Extends Round 50 with three high-alpha closures:
--
-- 1. G1 centre chart:
--      quantitative invariant-ball solution keeps the actual centre in 3/256;
--      input and centre in the same 3/256 operator-defect ball then give
--      ||U_j V^-1-I||_op <= 3/128 < 1/24 and hence
--      ||log(U_j V^-1)||_op <= 1/12.
--
-- 2. RG1d constrained differentiated-minimizer algebra:
--      the literal differentiated KKT pair is uniquely the existing finite
--      KKT Green solve once the same constrained coercivity is supplied.
--
-- 3. RG1e finite-lattice beta positivity:
--      beta = betaZ + betaInt,
--      betaZ >= b*, |betaInt| <= b*/2
--      => beta >= b*/2 and the source-oriented UV tube.
--
-- No GitHub Actions workflow is added or modified.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound50SourceChartResponseValidation
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreRelativeChartExact
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreInvariantBallExact
import DASHI.Physics.YangMills.BalabanYM4DifferentiatedKKTMinimizerExact
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact
