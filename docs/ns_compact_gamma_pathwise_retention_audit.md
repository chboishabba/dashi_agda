# Compact-Gamma pathwise retention audit

This lane tests whether the finite endpoint moduli from the retained-danger audit
can be resolved into stable local estimates along normalized packet paths.

The endpoint evidence had the form

```text
Gamma(member) - Gamma(center) <= L_Gamma d,
log(E(center) / E(member))_+ <= L_E d.
```

Here `E` is the positive compact-Gamma escape supply.  The pathwise audit asks
whether these bounds can be obtained by composing local segment estimates rather
than fitting only the two endpoints.

## Normalized path

For a center state `v` and member state `u`, both represented by reality-closed,
divergence-free Fourier coefficients, the sampled path is

```text
w_s = NormalizePacketEnergy((1-s) v + s u),  0 <= s <= 1.
```

Normalization keeps the selected shell packet energy fixed.  Every sample is
passed through the exact compact-Gamma snapshot and mechanism accounting used by
the preceding audits.

For adjacent path samples, the audit records

```text
Delta Gamma_+ / Delta ell
```

and

```text
Delta log(E)_- / Delta ell,
```

where `Delta ell` is physical Fourier-coefficient L2 distance.  Calibration paths
fit one-sided segment constants.  Held-out paths then test

```text
Gamma(member) <= Gamma(center) + L_Gamma length(path)
```

and

```text
E(member) >= exp(-L_logE length(path)) E(center).
```

The exponential form preserves positivity of the escape lower bound.

## Exact matched-cutoff reconstruction

The canonical entry point is

```text
scripts/ns_compact_gamma_pathwise_retention_driver.py
```

Selected held-out packets already carry the exact constructor seed that generated
their Fourier state.  Re-entering this seed through the generic split builder would
apply its seed-derivation convention a second time and silently construct another
packet.  The driver replaces only the `matched-member` and `matched-center`
builders so N32/N48/N64 checks preserve the original source seed.  Center,
calibration, and held-out finite-net construction remains unchanged.

## Formal bridge

`DASHI/Physics/Closure/NSCompactGammaPathwiseModulusComposition.agda` proves the
local-to-global algebra used by the experiment:

- adjacent additive Gamma allowances compose by addition;
- adjacent order-preserving escape-retention maps compose by function
  composition.

For real escape supplies the intended retention map is

```text
retain_delta(x) = exp(-delta) x.
```

The Agda theorem does not postulate or promote the empirical constants.

## Receipt authority

A successful receipt establishes only that:

- every sampled path branch was resolved;
- calibration produced finite local constants;
- the selected constants survived declared held-out paths;
- adverse paths were rechecked at the declared matched cutoffs and shells;
- mechanism, finite-difference, and normalization residuals stayed within the
  declared numerical tolerances.

The receipt explicitly leaves false:

- analytic pathwise Gamma Lipschitz authority;
- analytic pathwise log-escape Lipschitz authority;
- cutoff- and shell-uniform authority;
- continuum compactness authority;
- BKM, global-regularity, and Clay authority.

## Focused execution

```bash
python scripts/ns_compact_gamma_pathwise_retention_driver.py \
  --output-json ns-compact-gamma-pathwise-retention.json \
  --search-cutoff 24 \
  --verify-cutoffs 32,48,64 \
  --target-shells 2,3 \
  --triad-counts 4 \
  --phase-spreads 0.0,0.5 \
  --target-ratios 1.25,2.5 \
  --satellite-fractions 0.55 \
  --center-seeds 1 \
  --calibration-seeds 2 \
  --holdout-seeds 3 \
  --samples-per-base 1 \
  --path-sample-count 4 \
  --modulus-slack 0.2 \
  --pretty
```

The next analytic target is a shell- and cutoff-uniform differential estimate for
`Gamma` and `log E` on a normalized dangerous packet region, together with a
compact path-coverage theorem.
