# Event separation, time kernels, and quantisation formalism

`DASHI/Visualisation/EventSeparationQuantisationExact.agda` closes three finite obligations from the event-filament tranche without promoting them to continuum statistics.

## Robust local separation

A three-level comparison carrier admits an exact three-sample median. The canonical witnesses prove:

```text
median(near,middle,far) = middle
median(near,far,near)    = near.
```

An empty comparison neighbourhood has no mathematical median, so the model carries a declared fallback rather than silently assigning one. The fallback is `middle`, and the separation-to-sharpness code is increasing.

## External time and enlarged-space products

For a block-diagonal semantic/time kernel, the finite contribution is represented both as

```text
weight * semanticKernel * temporalKernel
```

and as

```text
weight * (semanticKernel * temporalKernel).
```

The canonical sample proves both routes equal `30`. This is an organisational equivalence for the product kernel; it does not imply that timestamps alone construct a trajectory.

## Componentwise quantisation

Exact and stored event parameters remain distinct records. The canonical parameter tuple has errors

```text
centre    1
scale     1
weight    0
sharpness 1.
```

Under the declared sensitivity tuple `(2,3,1,4)`, the finite field-error code is

```text
2*1 + 3*1 + 1*0 + 4*1 = 9.
```

This code is a checked finite budget, not a continuum Lipschitz theorem. A separate nonlinear-cell counterexample gives opposite-corner responses `2` and `4` but an interior response `11`, so two corners do not certify an enclosure.

The regression root is:

```text
DASHI/Visualisation/EventSeparationQuantisationRegression.agda
```
