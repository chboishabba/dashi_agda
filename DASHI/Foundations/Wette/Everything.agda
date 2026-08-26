module DASHI.Foundations.Wette.Everything where

-- Eduard Wette reconstruction rollup.
--
-- Keep source representation, executable-machine semantics, arithmetic
-- transition certification, finite mixed-rule traces, proof-carrying finite
-- derivability, representation/kernel transport, composed certified arithmetic
-- kernels, concrete arithmetic-machine witnesses, and metamathematical claim
-- boundaries separate so no stronger conclusion is imported merely by
-- importing the arithmetic coding layer.

import DASHI.Foundations.WetteArithmeticRepresentationExact
import DASHI.Foundations.WetteConstructiveAutomatonExact
import DASHI.Foundations.WetteArithmeticTransitionBridgeExact
import DASHI.Foundations.WetteFiniteDeductionTraceExact
import DASHI.Foundations.WetteRepresentationKernelBridgeExact
import DASHI.Foundations.WetteCertifiedArithmeticKernelExact
import DASHI.Foundations.WetteFRACTRANCrossPollinationExact
import DASHI.Foundations.WetteBernaysConsistencyDeductionBoundaryExact
import DASHI.Foundations.WetteFiniteDerivabilityBernaysBridgeExact
import DASHI.Foundations.WetteConsistencyClaimBoundaryExact
