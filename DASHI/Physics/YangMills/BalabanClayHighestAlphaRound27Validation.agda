module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound27Validation where

------------------------------------------------------------------------
-- Focused validation root for the round-27 finite-coercivity continuation:
-- signed scalar Wilson reduction; literal 18/6 incidence; exact W-local to
-- W-global and sharp-flat-Wilson transport; corrected physical/periodic carrier
-- conversions; selected-background same-h assembly to the 10739/196608 literal
-- Hessian coefficient; cubic Combes--Thomas shell arithmetic; discounted RG
-- loss tails; and the exact counterexample proving that the relaxed bondwise
-- radius alone does not imply the proposed W-local allocation.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound26Validation
import DASHI.Physics.YangMills.BalabanP33WilsonAtomSignedPerturbationExact
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLocalToSharpDefectExact
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact
import DASHI.Physics.YangMills.BalabanP33CubicShellSeriesExact
import DASHI.Physics.YangMills.BalabanP33PhysicalInfiniteDiscountedLossExact
import DASHI.Physics.YangMills.BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact
