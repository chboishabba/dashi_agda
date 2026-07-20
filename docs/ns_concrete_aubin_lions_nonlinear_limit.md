# Concrete Aubin–Lions and nonlinear-limit witnesses

`DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses` refines the existing Galerkin compactness interface into the requested G1–G19 dependency chain.

## Finite-dimensional Galerkin layer

The setting records the selected projected equation

`∂t u_N + P_≤N B(u_N,u_N) = ν Δu_N`,

its projected initial datum, and separate witnesses for global smooth finite-dimensional existence, uniqueness, the exact energy identity, the three-dimensional nonlinear `H⁻¹` estimate, and the uniform `L^(4/3)_t H⁻¹_x` time-derivative bound.

## Compactness and nonlinear identification

The certificate requires named witnesses for:

- Aubin–Lions strong `L²_t L²_x` convergence;
- weak `L²_t H¹_x` and weak-star `L∞_t L²_x` convergence;
- continuous convergence in a sufficiently negative Sobolev topology;
- finite-shell uniform convergence and packet-energy convergence;
- `L¹` product convergence and distributional nonlinear convergence;
- initial-trace identification;
- lower semicontinuity of dissipation;
- Leray–Hopf identification and the energy inequality.

## Compact-Γ passage

The functional layer separates numerator convergence, differentiated numerator convergence, the positive-denominator branch, the division-free zero-denominator continuation, modulus-budget lower semicontinuity, and passage of the cutoff estimate.

Weak–strong uniqueness is a final independent witness. It identifies the Galerkin limit with the selected strong path used by downstream closure theorems.

## Integration

`toCanonicalGalerkinCertificate` assembles all G1–G19 witnesses into the existing `GalerkinCompactnessAndLimitCertificate`. This makes the finer theorem chain available without breaking current consumers.

## Authority boundary

The module formalizes proof obligations and their dependency graph. It does not claim that finite Agda computation proves Aubin–Lions, global three-dimensional strong existence, or weak–strong uniqueness. Those analytic results must inhabit the corresponding predicates in a concrete Navier–Stokes model.