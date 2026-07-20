# Navier--Stokes Galerkin compactness and nonlinear-limit interface

`DASHI/Physics/Closure/NSGalerkinCompactnessLimit.agda` replaces the previous shape in which a single abstract convergence family could stand in for the full Galerkin passage.

The new interface is fail-closed. A complete certificate requires five named witnesses:

1. `GalerkinUniformBounds`
   - uniform energy estimate;
   - uniform time-derivative bound;
   - explicit cutoff uniformity for both.

2. `GalerkinSubsequenceCompactness`
   - an actual subsequence;
   - Aubin--Lions strong convergence in time-space `L2`;
   - weak gradient convergence;
   - weak time-derivative convergence;
   - finite-packet energy convergence, including the times or time norm needed downstream.

3. `NavierStokesNonlinearLimit`
   - strong--weak product identification;
   - convergence of the nonlinear term in distributions;
   - convergence of the projected nonlinear term;
   - initial-data identification;
   - Leray--Hopf identification;
   - strong-solution and uniqueness witnesses where a single path is required.

4. `CompactGammaFunctionalLimit`
   - compactness of tangent families;
   - convergence of the compact-Gamma numerator;
   - convergence of its tangent response;
   - denominator positivity on the active branch;
   - a zero-packet-energy branch;
   - a division-free identity and exact continuation alternative.

5. `BudgetLowerSemicontinuity`
   - lower semicontinuity of the dissipative `L2_t H1_x` quantity;
   - lower semicontinuity of the modulus budget;
   - the stronger budget convergence statement required by downstream arguments.

`GalerkinCompactnessAndLimitCertificate` can only be assembled from all five witnesses. Its projections expose the strong `L2` limit, nonlinear distributional limit, differentiated compact-Gamma limit, dissipation liminf, and denominator continuation alternative.

## Authority boundary

This module formalises the analytic dependency structure. It does not claim to derive Aubin--Lions, the Navier--Stokes nonlinear limit, denominator positivity, uniqueness, or lower semicontinuity from primitive functional analysis already available in the repository. Those results must be supplied as typed witnesses with the indicated content; an undifferentiated statement that “the Galerkin sequence converges” is no longer sufficient.
