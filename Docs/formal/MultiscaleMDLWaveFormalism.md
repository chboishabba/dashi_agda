# Multiscale residual, MDL, and wave-correspondence formalism

## Status

This tranche separates three levels of claim:

1. **Proved/interface-level core** — exact project/lift, exact residual reconstruction,
   exact kernel naturality, explicit symmetry-action witnesses, and exact
   natural-number description-length accounting.
2. **Proved 369 ultrametric consequence** — a kernel that preserves common-prefix
   agreement is non-expanding in the existing `SSP369Ultrametric` distance.
3. **Candidate physics bridge** — an explicit field/wave dictionary, continuum-limit
   obligations, and quantitative falsification contracts. No continuum PDE,
   Shannon optimality, or physical-law selection theorem is promoted.

## Canonical modules

- `DASHI.Core.MultiscaleMDL`
- `DASHI.Geometry.SSP369Ultrametric` (existing theorem spine)
- `DASHI.Geometry.SSP369KernelStability`
- `DASHI.Physics.MultiscaleWaveCorrespondence`
- `DASHI.Physics.MultiscaleWaveCorrespondenceRegression`

## Core object

A `MultiscaleCarrier` supplies scale-indexed carriers `Carrier j`, projection,
lift, and the section law

```text
project (lift x) = x.
```

A `ResidualCodec` does not assume that states form a ring or vector space.
Instead, it supplies a residual carrier and the exact reconstruction law

```text
reconstruct (project x) (residual x) = x.
```

This is the application-neutral content shared by predictive codecs,
supervoxel towers, hierarchical reasoning carriers, and possible field
instantiations. Ring-valued difference residuals are one later instance, not a
hidden primitive.

A `KernelTower` supplies scale-indexed updates and exact naturality

```text
project (kernel (suc j) x) = kernel j (project x).
```

Approximate commutation requires a selected metric and explicit error bound; it
is not represented as equality.

A `SymmetryAction` carries explicit action witnesses. `OrbitRelated x y` means
that a concrete symmetry maps `x` to `y`. The core does not postulate quotient
types or silently identify symmetry-related values.

An `MDLCost` supplies natural-number code lengths for the coarse state and
residual. `stepDescriptionLength` is exactly their sum. Calling this quantity
MDL does **not** prove a Kraft inequality, entropy bound, minimax regret bound,
or rate-distortion optimality; those require probability/coding hypotheses in
a later module.

## Ultrametric stability theorem

The existing `SSP369Ultrametric` defines distance as

```text
depth - agreementDepth x y.
```

`PrefixMonotoneKernel` requires

```text
agreementDepth x y <= agreementDepth (K x) (K y).
```

`distance-nonexpanding` then proves

```text
distance (K x) (K y) <= distance x y.
```

This is a precise theorem-level reading of stable/pruned arms. It does not yet
imply convergence to a unique fixed point. The stronger
`StrictPrefixContractingKernel` interface records the missing strict-distance
premise. A complete fixed-point closure still needs a finite-descent or
completeness theorem appropriate to the chosen tower.

## Physics correspondence

The candidate dictionary maps:

| Formal role | Candidate physical reading |
| --- | --- |
| scale index | spatial resolution |
| cell index | spatial cell |
| carrier value | field amplitude/components |
| projection | conservative averaging |
| lift | interpolation/replication |
| residual | sub-grid fluctuation |
| kernel | discrete evolution step |
| description length | coding/model-selection penalty |
| symmetry orbit | representational redundancy/gauge candidate |
| prefix distance | first differing scale |

Every row is explicitly marked as an interpretation, not a definition or
physical theorem.

The initial continuum target is a three-spatial-dimensional, two-component
first-order wave system. Promotion requires:

- a concrete local stencil;
- consistency estimate as grid spacing tends to zero;
- stability estimate with an explicit time-step condition;
- convergence proof;
- dimensional/units interpretation;
- empirical comparison.

The current status deliberately records `continuumPDEDerived = false`.

## Falsification contracts

The bridge names three quantitative tests:

1. **Dispersion:** phase/group-velocity error must decrease at the predicted
   convergence order under refinement.
2. **Rate-distortion:** bits per symbol at fixed distortion must be reported
   against a named strong domain baseline; no Shannon claim follows merely from
   using residuals.
3. **Scale commutation:** the measured defect between projected fine evolution
   and coarse evolution must decrease or remain within a proved bound.

Until measurements and bounds are supplied, all benchmark and physics
promotion flags remain false.

## Relationship to broader DASHI language

- “Difference manifold” is normalized here to an exact coarse/residual
  decomposition. A geometric manifold structure requires additional charts,
  topology, and compatibility proofs.
- “Stable multiverse arm” can be read mathematically as a stable orbit, branch,
  or fixed-point basin only after the state space, update, equivalence relation,
  and stability criterion are specified.
- “Hyper-exponential pruning” remains a complexity claim requiring a counted
  search procedure and asymptotic bound.
- “Shannon optimality” remains a coding theorem target, not a consequence of
  MDL terminology.
- “Physical-law selection” remains a hypothesis requiring a model class,
  selection theorem, continuum map, and falsifiable observations.

This keeps the geometric intuition available while preserving the repository's
proved/bridge/empirical/speculative boundary.
