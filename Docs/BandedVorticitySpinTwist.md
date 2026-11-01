# Banded vorticity spin/twist carrier

## Status

Candidate-only fluid/codec bridge. This tranche does **not** prove Navier–Stokes closure, an inertial manifold, trajectory accuracy, or exact continuum-vorticity recovery.

## Why this exists

The experimental CFD path currently has two materially different use cases:

1. a fast reconstruction that retains low-frequency geometry and aggregate mid/high residual information;
2. a vortex-faithful reconstruction for domains where circulation sign, vortex placement, shedding, transport, or coherent-structure identity matters.

The former may synthesize unresolved texture from band-energy summaries. That can be useful and fast, but aggregate energy plus a support mask does not contain the phase/location information needed to identify particular vortices. The latter therefore needs an explicit spatial signed carrier.

## Formal carrier

`DASHI.Physics.Fluid.BandedVorticitySpinTwist` composes existing repository ideas rather than introducing a parallel ternary language:

- it reuses `DASHI.Foundations.SSPTritCarrier` for the canonical `-1 / 0 / +1` values;
- `ScaleBand` supplies the independent `low / mid / high` spectral or resolution index;
- `spinSupport` factors support from sign: `0` is unsupported/neutral, while `-1` and `+1` are supported opposite orientations;
- `BandedSpinTwistSample` adds periodic spatial placement and a coarse amplitude level;
- `VortexAtom` requires nonzero support and carries core-scale and circulation-level proxies;
- `PeriodicBoundaryContract` makes the toroidal boundary assumption explicit, preventing an unannounced non-periodic smoother from entering an FFT/wrapped-neighbourhood lane.

The two ternaries must not be conflated:

```text
low / mid / high       = scale band
-1 / 0 / +1            = signed spin/twist state at that band and site
```

## Two solver modes, one refinement relation

### Fast mode

`FastResidualState` carries:

- aggregate energy by band;
- an aggregate support fraction;
- a texture seed.

Its admitted capability is aggregate band statistics / texture reconstruction. It is fail-closed for spatial vortex identity.

### Vortex-faithful mode

`FaithfulResidualState` carries the same aggregate summaries plus a sparse list of spatially placed signed `VortexAtom`s. Its admitted capabilities include spatial vortex identity and signed skeleton transport at the level of this finite carrier.

### Explicit quotient

`eraseFaithfulResidual` and `eraseFaithfulState` forget atom placement while preserving:

- the shared low-band carrier;
- aggregate band energy;
- aggregate support fraction.

The accompanying proofs make the fast state an explicit quotient of the faithful state rather than a separate solver ontology.

## Relation to existing DASHI lanes

This module is intentionally downstream of the canonical SSP trit carrier and aligned with the repository’s recurring distinctions:

- carrier versus interpretation;
- support versus polarity;
- resolved state versus bounded residual;
- theorem spine versus empirical bridge;
- explicit erasure/quotient versus silent information loss;
- fail-closed promotion boundaries.

It also complements the existing Navier–Stokes audit lane described in the root README. It does not strengthen the helical-triad, seam-to-leakage, pressure/coercivity, or global-regularity claims.

## Regression witnesses

`DASHI.Physics.Fluid.BandedVorticitySpinTwistRegression` constructs:

- one negative mid-band atom;
- one positive high-band atom;
- a shared low-band carrier;
- a vortex-faithful state;
- its erased fast state;
- definitional proofs that erasure preserves the low carrier, band energies, and support summary.

## Intended implementation handoff

A numerical backend can now expose both paths against the same typed contract:

```text
FAST:
  low coefficients
  + per-band energy/support summaries
  -> aggregate-correct residual texture

VORTEX-FAITHFUL:
  low coefficients
  + per-band signed support
  + sparse position/core/circulation atoms
  -> coherent-vortex reconstruction

ERASE:
  vortex-faithful state -> fast summary
```

Future quantitative receipts should measure, separately:

- energy/enstrophy and spectral error for both modes;
- vortex-core position, sign, circulation, and lifetime for faithful mode;
- atom count / description length versus accuracy;
- periodic-boundary seam diagnostics;
- the domain-specific gate deciding when fast mode is admissible.
