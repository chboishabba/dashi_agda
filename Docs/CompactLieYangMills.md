# Compact Lie groups in the DASHI Yang–Mills route

This surface separates three obligations that were previously easy to conflate:

1. exact algebra and lattice identities that Agda can check locally;
2. standard finite-dimensional compact-Lie-group theorems imported through an explicit authority socket;
3. conditional and conjectural analytic targets required by the four-dimensional Balaban/Clay route.

## Proof levels

`CompactLieProofLevel.agda` defines five levels:

| Level | Meaning | Locally promotable |
|---|---|---|
| `computed` | definitional or normalized computation | yes |
| `machineChecked` | theorem proved from repository inputs | yes |
| `standardImported` | established external theorem, isolated at an authority boundary | no |
| `conditional` | theorem proved after named hypotheses are supplied | no |
| `conjectural` | exact target type with no witness yet | no |

A conjectural record is executable theorem **shape**, not evidence that the theorem holds.

## Machine-checked layer

The exact surface proves or assembles:

- ordinary consequences of the group axioms, including cancellation, inverse involution, conjugation, and internal-vertex cancellation;
- path-holonomy gauge covariance for an arbitrary group and arbitrary directed lattice;
- gauge invariance of every closed-loop class-function observable;
- structural covariance of transported-log block averaging;
- repeated-commutator majorants from a single bracket constant;
- the Cartan-family rank, dimension, and dual-Coxeter formulas as total computations;
- a concrete `SU(2)` Lie algebra over the existing imaginary-quaternion carrier, including bilinearity and Jacobi;
- a concrete generic adjoint representation, with exact identity, product, linearity, and bracket-automorphism laws proved from quaternion multiplication;
- weighted-column estimate to pointwise exponential kernel decay;
- `C_G L_N ≤ ρ` plus the local critical-map estimate to a contraction estimate at `ρ`;
- assembly of fixed-point/critical-point, minimizer, gauge-orbit, and analytic-dependence interfaces into the background-field package.

The quaternion rotation polynomials therefore become a concrete implementation of generic `Ad`, rather than a dependency of the generic theory.

## Concrete SU(N) matrix lane

The next surface adds a finite-matrix presentation that is independent of quaternion accidents:

- `SUNMatrixCarrier.agda` defines special-unitary matrices by the equations
  `U†U = I`, `UU† = I`, and `det U = 1`, then assembles the group structure;
- `SUNMatrixLieAlgebra.agda` defines traceless anti-Hermitian matrices and the commutator bracket, then assembles the Lie algebra;
- `SUNMatrixLieGroup.agda` defines matrix conjugation as `Ad`, and assembles the compact-simple Lie-group interface from explicit topology/exponential authority;
- `SUNMatrixGeometry.agda` assembles the invariant trace metric, bi-invariant distance, quantitative local exponential chart, and group-dependent bracket/adjoint constants;
- `SU3MatrixInstance.agda` fixes `N = 3` and computes `dim su(3) = 8`;
- `SUNWilsonClassFunction.agda` turns normalized real trace into a checked class function and instantiates closed-loop gauge invariance;
- `SUNWilsonAction.agda` defines the finite plaquette sum and proves gauge invariance of the full Wilson action by induction over plaquettes.

Finite complex-matrix algebra, determinant identities, compactness, connectedness, simplicity, exponential-chart facts, and cyclicity of trace are `standardImported`. The subtype construction and all group/Lie/metric/chart/Wilson record assembly are `machineChecked`.

## Standard imported layer

`CompactLieAnalyticPackage.agda` states the actual theorem interfaces for:

- an invariant positive metric and bi-invariant group distance;
- a quantitative local exponential/logarithm chart;
- BCH with a cubic remainder bound;
- normalized Haar integration;
- Peter–Weyl orthogonality, completeness, Weyl integration, and character bounds.

`CompactLieStandardAuthority.agda` is the sole imported theorem socket for these classical facts. It also provides the explicitly named imported `SU(2)` analytic package. These witnesses are deliberately not marked locally promotable.

## Constructive analytic stack

`ConstructiveYangMillsNextSurface.agda` compiles the next proof chain in the order in which the mathematics must close:

1. `BalabanFiniteInverseConsequences.agda` derives injectivity and uniqueness from the finite Hessian/Green inverse certificate;
2. `BalabanFiniteVolumeBackgroundLane.agda` factors the critical-map estimate into patchwise Green constants, nonlinear Lipschitz constants, local factors, and a strict common factor;
3. `BalabanOneStepRGClosure.agda` requires fluctuation coordinates, Jacobian/determinant control, BCH control, Ward identities, localization, vacuum-energy and coupling renormalization, and a bounded irrelevant polymer remainder;
4. `BalabanStepVKPClosure.agda` separates polymer activity, entropy, suppression, and the final Kotecký–Preiss comparison;
5. `BalabanAllScaleRGClosure.agda` proves the exact induction from one-step invariant-domain preservation to admissibility at every finite scale;
6. `BalabanOSMassGapClosure.agda` separates continuum OS axioms, standard OS reconstruction, uniform clustering, and the physical spectral-gap transfer;
7. `BalabanDashenGrossCalibration.agda` makes the generator, lattice-spacing, determinant, and coupling-scheme normalization factors explicit and proves the final convention map from their calibrated product.

These modules prove the logical bridges and keep the analytic antecedents explicit. No large-field, all-scale, OS, or mass-gap premise is silently manufactured.

## Proof-level audit

`scripts/audit_constructive_yang_mills_levels.py` runs before the focused Agda check. It verifies that the locally checked assembly modules contain no `postulate`, authority boundaries retain `standardImported`, frontier fields retain `conditional` or `conjectural`, and the Clay promotion flag remains explicitly false.

## Conditional and conjectural frontier

Conditional inputs:

- concrete all-patch weighted Green estimates;
- nonlinear residual Lipschitz constants;
- constrained Hessian coercivity;
- nonlinear gauge-fixing contraction;
- the fully instantiated background-field closure;
- one-step fluctuation, determinant, Ward, localization, and polymer estimates.

Conjectural targets:

- one strict residual factor `ρ_G < 1` uniform in scale, volume, admissible background, and patch regime;
- four-dimensional large-field / Step V polymer suppression;
- an all-scale four-dimensional RG invariant domain with summable errors;
- continuum Schwinger functions satisfying OS0–OS5;
- an OS-reconstructed Hamiltonian with a positive physical spectral gap.

The final mass-gap target has no constructor here and cannot self-promote.

## Quantifier discipline

The intended theorem is group-parametric:

```text
for every compact simple G
there exist group constants ε_G, μ_G, ρ_G, C_G
such that the estimates are uniform in lattice scale, volume,
background, and patch regime.
```

It does **not** demand a single numerical constant uniform over all compact simple groups.

## Canonical surfaces

- `CompactLieExactSurface.agda`: exact locally checked mathematics.
- `CompactLieAnalyticPackage.agda` and `CompactLieStandardAuthority.agda`: standard imported analysis.
- `CompactLieYangMillsFrontier.agda`: conditional/conjectural theorem ledger.
- `ConstructiveYangMillsNextSurface.agda`: concrete SU(N) and constructive analytic closure stack.
- `CompactLieTheorySurface.agda`: aggregate compilation surface.

No module in this stack sets the repository’s Clay Yang–Mills promotion flag.
