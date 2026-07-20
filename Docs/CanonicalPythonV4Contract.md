# Canonical Python v4 numerical contract

This note connects the merged banded-vorticity formalism to the current canonical Python path in `chboishabba/dashiCFD`:

- `run_v4_snapshots.py`
- `dashi_cfd_operator_v4.py`

It records implementation facts rather than inferring mathematical claims from plots.

## What is implemented

The current proxy/decoder carries:

- periodic FFT differentiation and Poisson inversion;
- retained low-band complex Fourier modes;
- retained top-K mid-band complex residual modes;
- aggregate remaining-mid and high-band energy summaries;
- ternary support/sign masks;
- deterministic frame-indexed residual RNG seeding in the canonical runner;
- an optional periodic Gaussian vortex-atom splat during decode.

The top-K mid-band channel is important: the decoder is no longer wholly phase-free. It retains some concrete phase-bearing geometry. The remaining unresolved mid/high content is still synthesized statistically.

## Concrete mismatches and blockers

### Periodic PDE, non-periodic smoother

The spectral PDE is periodic, but `smooth2d` uses one-dimensional `np.convolve(..., mode="same")` passes. This does not wrap the torus and can create edge-local bias in initialization and support-mask construction.

### Real-field residual synthesis

The synthesized random spectrum does not explicitly construct conjugate/Hermitian symmetry before inverse FFT. The implementation then returns the real part. Post-gating energy is rescaled, but a theorem-facing real-field and band-energy tolerance contract is not yet present.

### Decode hook is not a faithful pipeline

The optional atom loop can rasterize supplied atoms. The canonical runner does not currently:

1. extract atoms from vorticity;
2. estimate normalized circulation and core radius;
3. transport atoms;
4. associate identities across periodic frames;
5. handle births, deaths, merges, and splits;
6. pass tracked atoms into the end-to-end decode.

### `gamma` semantics

The current Gaussian contribution multiplies the kernel by `sign * gamma`. Unless the kernel is normalized by its discrete integral, `gamma` is a peak-amplitude parameter rather than certified circulation.

### Evaluation split

The canonical demonstration learns the linear proxy operator from the encoded trajectory and rolls out against that same trajectory. This is an in-sample diagnostic, not held-out generalization evidence.

## Formal result

`DASHI.Physics.Fluid.CanonicalPythonV4Contract` records implemented and blocked features separately.

Fast-mode promotion requires:

- periodic smoothing;
- real/Hermitian residual synthesis;
- held-out evaluation;
- an application-specific adequacy receipt.

Faithful-mode promotion additionally requires:

- normalized circulation rasterization;
- atom extraction;
- atom transport;
- substantive temporal association.

Both promotion gates are currently constructively blocked by absent implementation witnesses.

## Required measurements

The fast route must report at least field error, correlation, spectral error, energy, enstrophy, support fraction, temporal correlation, runtime, memory, and description length.

The faithful route additionally requires core-position error, circulation error, track survival, and merge/split accuracy.

These are measurement obligations, not fixed universal tolerances. Each application must supply its own adequacy threshold.

## Next executable tranche

The recommended order is:

1. periodic smoother plus seam/translation-equivariance tests;
2. conjugate-symmetric real residual synthesis and measured band-energy tolerances;
3. normalized periodic Gaussian atom rasterizer;
4. signed 2D core extraction;
5. periodic frame association and simple birth/death/merge/split receipts;
6. held-out comparison of fast, faithful, and hybrid modes;
7. machine-readable promotion receipt.

This remains a finite implementation contract. It is not a Navier–Stokes closure theorem, inertial-manifold theorem, or continuum Lie/gauge equivalence.
