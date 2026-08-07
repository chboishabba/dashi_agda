# Requirements, preconditions, postconditions and invariants

[Back to the contract overview](README.md)

## Official target

This route targets Fefferman’s periodic alternative (B).

For every positive viscosity and every smooth divergence-free datum on the unit three-torus, with zero external force, produce velocity and pressure defined for all nonnegative time such that both are smooth and spatially periodic, the three-dimensional Navier–Stokes momentum equation holds, the velocity remains incompressible and the initial datum is attained at time zero.

Pressure periodicity is included explicitly because it is stated in the official erratum.

Mean-zero data, uniqueness, an energy equality and a pressure normalization are useful proof-route properties but are not official preconditions or postconditions of alternative (B).

## Preconditions

| Clause | Contract state | Meaning |
|---|---|---|
| Positive viscosity | Exact target | The theorem quantifies over arbitrary viscosity with a positivity witness. |
| Dimension three | Exact target | The carrier is specialized to the three-dimensional equation. |
| Unit three-torus | Exact target | Datum, velocity and pressure periodicity are all represented. |
| Zero external force | Exact target | The momentum predicate is the zero-force equation. |
| Arbitrary smooth datum | Exact target | No smallness or special-symmetry assumption is present. |
| Divergence-free datum | Exact target | This is the official incompressibility precondition. |
| Unit-periodic datum | Exact target | The initial datum is periodic in all three coordinates. |
| Mean zero | Not a Clay precondition | Centering is handled by Galilean reduction. |

## Postconditions

| Clause | Contract state | Meaning |
|---|---|---|
| Global velocity | Exact target | Defined for every nonnegative time. |
| Global pressure | Exact target | Defined for every nonnegative time. |
| Smooth velocity | Exact target | Smooth on the three-torus times the nonnegative time axis. |
| Smooth pressure | Exact target | Smooth on the same domain. |
| Velocity periodicity | Exact target | Unit-periodic in each spatial coordinate. |
| Pressure periodicity | Exact target | Explicitly required from the official erratum. |
| Momentum equation | Exact target | Three-dimensional Navier–Stokes with selected viscosity and zero force. |
| Incompressibility | Exact target | Divergence free for all nonnegative time. |
| Initial trace | Exact target | Velocity attains the supplied datum at time zero. |
| Uniqueness | Not required by alternative (B) | It may be retained after pressure normalization but is not part of the target. |
| Periodic finite-energy bound | Not required by alternative (B) | It is automatic for smooth periodic velocity on a compact torus and need not be added to the statement. |

## Proof-route invariants

These are not extra Clay hypotheses. They are controls that every intermediate theorem must preserve.

1. Divergence-free Galerkin evolution.
2. Periodic translation structure for velocity, pressure, filters and kernels.
3. Constants uniform in shell cutoff, Galerkin cutoff and hypothetical maximal time.
4. Critical Navier–Stokes scaling.
5. Exhaustive named source decomposition with no unnamed residual.
6. Pair-input-frequency diffusion retained before high-high products collapse to low output.
7. Only positive critical production is taxed.
8. Total viscosity tax is strictly below one.
9. No uncontrolled critical supremum appears on the right-hand side.
10. No BKM or Serrin norm is assumed on the uncontrolled side.
11. No alignment, coherence, finite-residence or small-data hypothesis is assumed.
12. Nonlinear terms are absorbed before weak or compactness limits are taken.
13. Shell and Galerkin limits retain their correct quantifier order.
14. A bounded critical norm feeds a standard local restart theorem.
15. Centering and Galilean restoration preserve the exact Clay postconditions.
16. Pressure recovery preserves smoothness and periodicity.

## Current in-repository path state

### Implemented target or reducers

- Literal Fefferman periodic theorem type.
- Finite Galerkin critical filtered-enstrophy identity.
- Pair-input-frequency damping and the high-high-to-zero-output counterexample to output-frequency damping.
- Five-source tax algebra once physical estimates are supplied.
- Critical-production absorption and Grönwall reservoir algebra.
- Nested shell/Galerkin selection logic with separate positive margins.
- Maximal-time contradiction from a critical restart interface.
- Legacy submission witness to literal Fefferman witness adapter.
- Mean-zero-to-arbitrary-data Galilean quantifier reduction.
- End-to-end terminal composition after all physical producers are supplied.

### Load-bearing open producers

1. Actual finite Fourier/Galerkin mode enumeration and Bony support exhaustiveness.
2. Uniform physical estimates for advection, stretching, subgrid, kernel and tail sources.
3. Scale-uniform positive-variation bound for hysteretic bad-state re-entry.
4. Navier–Stokes-derived dissipation-wavenumber high-mode amplitude condition.
5. Critical bound for the low-frequency reservoir.
6. Periodic principal-value strain kernel, actual sphere-moment theorem and Calderón–Zygmund estimate.
7. Continuum filter-increment-to-diffusion coercivity with a scale-uniform coefficient.
8. Uniform geometric ratios for far-field, commutator and cutoff tails.
9. Strict combined coefficient below one.
10. Analytic shell convergence and Galerkin convergence in the required critical topology.
11. Local critical restart theorem connected to the selected physical carrier.
12. Smooth pressure recovery, pressure periodicity and higher-Sobolev bootstrap.
13. Continuum spatial mean and verification of Galilean invariance for the exact carrier.
14. Concrete adapter between the repository’s legacy solution carrier and the literal Fefferman carrier.

## Acceptance tests for any proposed producer

A producer advances the route only when all of the following pass:

- it is valid for arbitrary smooth periodic data;
- it has the correct Navier–Stokes scaling;
- its constants are uniform in every active cutoff;
- it introduces no hidden target norm on the right;
- it identifies every residual term;
- its viscosity allocation is explicit;
- its result composes with the existing downstream theorem without a new hypothesis;
- a finite rational or Fourier-mode counterexample search does not falsify it;
- the Agda module contains no postulate, hole, trust primitive or unsafe escape;
- the cumulative validation root typechecks before promotion.
