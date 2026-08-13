module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound50SourceChartResponseValidation where

------------------------------------------------------------------------
-- Focused Round-50 validation root.
--
-- Extends Round 49 with the source-faithful CMP98 operator-norm correction,
-- square-root-free physical quaternion defect bounds, minimal length-24 chart
-- budgets, conservative Lie3 l1 quadratic-96 transport, exact differentiated-
-- minimizer Green response/remote locality, and the source-oriented CMP109
-- inverse-coupling recurrence/two-sided UV tube.
--
-- No GitHub Actions workflow is added or modified.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound49CoupledRGValidation
import DASHI.Physics.YangMills.BalabanCMP98Lie3L1NormTransportExact
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1DefectExact
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1SharpExact
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSelectedYRadiusExact
import DASHI.Physics.YangMills.BalabanCMP98PerturbationScaleSourceXRadiusExact
import DASHI.Physics.YangMills.BalabanCMP109Federbush011OperatorNormToLie3L1Exact
import DASHI.Physics.YangMills.BalabanYM4DifferentiatedMinimizerGreenResponseExact
import DASHI.Physics.YangMills.BalabanYM4DifferentiatedMinimizerRemoteLocalityExact
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact
