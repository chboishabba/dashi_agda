# Cutoff-uniform integer-shell Schur programme

`DASHI.Physics.Closure.NSCutoffUniformIntegerShellSchur` refines the existing exact finite pair-incidence/full-shell kernel lane into the nine proof obligations needed for a genuinely cutoff-uniform theorem.

## Ownership

- `IntegerShellEnumeration` owns SC1 and SC2: dyadic shell cardinality, weighted shell sums, radial tails, literal cutoff stabilization, and stabilization of every finite fold after the cutoff exceeds its largest participating shell.
- `ResonantPairEnumeration` owns SC3 and SC4: the `q = k - p` parametrization, sound/complete/duplicate-free shell-pair enumeration, exact cutoff admissibility, and nonzero witnesses for every denominator-bearing mode.
- `WeightedShellConvolution` owns SC5, including a separate endpoint-logarithmic leaf rather than silently using the non-endpoint decay formula.
- `CutoffUniformFullShellKernel` owns SC6, SC7, and SC8. Its row and column budgets do not depend on `K` or `N`; cutoff extension is equality of kernel entries on the smaller carrier.
- `SquaredSchurAction` contains only the domain-neutral weighted Schur algebra.
- `uniformFullShellSchurSquared` is SC9. It derives the squared operator estimate from SC6 and SC7 with constant `C_row * C_col`.

## Relation to the existing repository

The module reuses `NSCompactGammaFullShellSchur.fullShellKernelAt`, so it does not create a second kernel representation. The exact pair-incidence fold remains the canonical finite kernel; the new layer states what must be proved about the integer lattice and cutoff family before that finite kernel yields a theorem uniform in target shell and Galerkin cutoff.

The programme is re-exported by `NSPairIncidenceKernelProgram`.

## Proof boundary

This change exposes and composes SC1--SC9 without pretending that the concrete `Z^3` estimates have already been discharged. A concrete lattice instance must still instantiate the proof-relevant records with:

1. actual dyadic cardinality and weighted-tail proofs;
2. the repository's concrete resonant-pair list and its completeness/no-duplicate proofs;
3. differentiated Biot--Savart convolution exponents and endpoint logarithms;
4. exact row/column bounds for the selected near-shell weights.

Once those leaves are supplied, SC9 is no longer an assumption: `uniformFullShellSchurSquared` produces the final cutoff-uniform squared norm inequality directly.
