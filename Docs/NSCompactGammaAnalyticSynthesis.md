# Compact-Gamma analytic synthesis

This tranche integrates the compact-Gamma work that landed independently through the differentiated-triad, Schur-tail, Galerkin, invariant-region, and BKM branches.

## Dependency chain

```text
exact Fourier/Biot-Savart triad
  -> differentiated local majorant
  -> finite full-shell incidence kernel
  -> exact weighted row/column sums
  -> near-shell Schur control
  -> quantitative far-shell decay
  -> finite-cutoff D log E modulus
  -> actual Galerkin compactness/nonlinear identification
  -> compact-Gamma invariant region
  -> derived vorticity expenditure
  -> BKM continuation
```

## Cross-pollinated owners

### Differentiated triads

`NSDifferentiatedTriadAnalyticLeaf` owns the pointwise Biot-Savart, projected-interaction, differentiated-product, reality-folding, tangent-projection, and compact-Gamma coefficient surfaces.

`NSCompactGammaDifferentiatedTriadInstantiation` identifies every concrete pair atom with that analytic leaf. Its local majorization proof is therefore derived from `concrete-differentiated-triad-bound`; it is no longer a free field in the finite summation record.

### Full shell

`NSCompactGammaFullShellSchur` replaces an arbitrary scalar-valued row/column boundary with an exact `FiniteWeightedKernel` at every shell and cutoff.

The kernel owns:

- target and source enumerations;
- enumeration soundness, completeness, and duplicate exclusion;
- the full incidence relation and proof uniqueness;
- the actual local Fourier response and majorant;
- the exact weighted kernel entry and zero off-incidence;
- row and column weights.

Consequently `rowWeightedSum` and `columnWeightedSum` are definitionally the finite sums over the declared full carrier. A `FullShellUniformSchur` value must provide a Schur certificate for those exact sums at every `(K,N)`.

The combinatorial construction is split into named leaves: lattice shell counting, radial summability, angular/polarization control, zero-mode exclusion, cutoff monotonicity, and cutoff-uniform constants.

### Tail

`NSCompactGammaOffPacketTailDecayBridge` already separates high-high/high-low paraproduct decay, the decisive far-low commutator cancellation, the discrete `Z^3` dyadic convolution comparison, tangent-norm domination, and a geometric rate `epsilon(R) = C 2^(-alpha R)`.

The final synthesis requires a `UniformAnalyticTailDecay`, not only the weaker order-theoretic “eventually below every budget” record. The latter is derived from the quantitative estimate.

### Galerkin limit

The synthesis consumes `ActualGalerkinCompactGammaFamily`, which separately requires:

- cutoff-uniform energy/dissipation and time-derivative bounds;
- an Aubin-Lions subsequence and weak-gradient convergence;
- nonlinear distributional identification and solution-path uniqueness;
- packet, compact-Gamma numerator, and tangent-response convergence;
- denominator positivity or an exact division-free continuation branch;
- dissipation and modulus-budget lower semicontinuity.

The old opaque two-scalar convergence seam is not accepted.

### Invariant region

`NSCompactGammaAdmissiblePreservation` defines the actual admissible class using gamma and packet-energy floors, state-size and off-packet ceilings, reality, and divergence freedom.

`AdmissibleInvariantRegionCertificate` requires continuity, the inward boundary estimate, logarithmic-energy control, and packet-energy positivity separately. The no-first-exit witness must be derived from those leaves. Simultaneous shell preservation and cutoff-uniform Galerkin-to-limit preservation are both retained.

### Time integrability

`NSCompactGammaBKMTimeIntegrability` derives finite envelope expenditure from energy/dissipation, compact-Gamma inequalities, Bernstein shell estimates, weighted shell summation, and an explicit no-BKM-Sobolev-bootstrap certificate. It consumes BKM only at the final continuation step.

`CompactGammaBKMCoherence` records the commuting path map between that self-contained BKM carrier and the invariant-region path.

## Final owner

`NSCompactGammaAnalyticClosureProgram.CompactGammaAnalyticClosure` is the integrated proof-relevant package. It exports:

- local differentiated near-response majorization;
- exact full-shell weighted row and column estimates;
- the quantitative tail estimate and its order-vanishing consequence;
- continuum passage of the finite-cutoff logarithmic modulus;
- preservation of every selected compact-Gamma shell;
- Galerkin admissibility passage to the limit;
- BKM continuation.

## Authority boundary

This integration removes stale and under-specified interfaces. It does not fabricate the remaining real-analysis inhabitants.

In particular, the following still require concrete proofs for the actual integer Fourier/Navier-Stokes carrier:

- the real/normed component laws used by the differentiated-triad leaf;
- complete full-shell enumeration and incidence construction;
- lattice shell-counting, angular, and weighted Schur estimates uniform in cutoff;
- high-frequency paraproduct decay and far-low commutator cancellation;
- Aubin-Lions and nonlinear-limit witnesses for the chosen solution class;
- inward-pointing compact-Gamma boundary estimates with sufficient expenditure margin;
- Bernstein-weighted shell summability and finite envelope expenditure without circular use of BKM.

No global-regularity or Clay promotion follows until one concrete value of the integrated package is constructed from those analytic theorems.
