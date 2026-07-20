# Unified physical real/complex RG/CFT route

## Purpose

The shift fixed-point lane now has exact finite and inhabited reference models,
but those models use heterogeneous carriers: a three-state idempotent tangent,
a finite GF(2) complete reference, Nat-valued dimensions, finite insertion sites,
and a symbolic stream-valued depth envelope.

`PhysicalRealComplexRGCFTRoute.agda` defines the stronger object needed for a
physical promotion. Every lane must share one declared real or complex scalar
and one operator sector.

```text
one R/C scalar authority
  -> physical Banach tangent
  -> real-time Frechet flow and analytic generator estimates
  -> measured engineering/anomalous dimensions
  -> singular position-dependent OPE and conformal blocks
  -> real/complex analytic depth convergence
  -> RG universality across depth/regulator/scheme
  -> nontrivial stress tensor, central charge, and Ward identities
  -> cross-layer compatibility laws
  -> empirical validation authority
  -> physical promotion receipt
```

## Typed physical obligations

### Banach tangent

The physical tangent must provide a vector space over the shared R/C scalar,
a definite homogeneous norm, a norm-induced distance, a Cauchy/convergence
notion, completeness, and an explicit identification with the finite shift
sector.

### Real-time derivative and generator

The route requires nonlinear and linearized real-time flows, semigroup laws,
strong continuity, a linear Frechet derivative, a controlled remainder,
generator strong limits, exponential/dissipative bounds, and sectorial
resolvent estimates.

### Measured dimensions

Each scaling datum carries source and dataset identifiers, engineering and total
dimensions, uncertainty, analysis method, and renormalization scheme. The route
requires uncertainty-aware agreement, covariance/error authority, scale control,
and independent provenance.

### Singular OPE and conformal blocks

The continuum OPE target requires a separation-dependent singular kernel,
analyticity away from coincidence, OPE convergence, conformal-block convergence,
locality, crossing, common-domain associativity, and positivity or an explicitly
declared replacement.

### Analytic depth and RG universality

The balanced-ternary depth model must be scalarized into the shared R/C carrier.
Finite approximants must converge analytically, the depth metric must be complete,
and first-difference/cylinder estimates must be quantitative. RG control must
then prove finite-step intertwining, attraction, regulator independence, scheme
change equivalence, and universality on a declared basin.

### Stress tensor and Ward identities

The stress-tensor target requires nonzero central charge, a nontrivial stress
two-point function, distributional conservation, trace/anomaly accounting,
translation/rotation/dilation/special-conformal Ward identities, compatibility
with the singular OPE, and agreement of the central term with the stress OPE.

## Promotion boundary

`PhysicalRGCFTEmpiricalAuthority.agda` requires provenance, uncertainty audits,
independent authority, competing-model comparison, and falsification criteria.
A physical promotion can only be constructed from both:

1. an inhabited `PhysicalFixedPointRGCFTRoute`; and
2. a matching `PhysicalRGCFTValidationAuthority`.

`ShiftPhysicalRGCFTHandoff.agda` integrates this target with the existing shift
reference route and keeps promotion empty. The repository therefore has a
complete theorem-facing physical target, but it does not claim that measured
anomalous dimensions, singular continuum OPE data, real/complex convergence,
universality, central charge, or a physical CFT have been established.
