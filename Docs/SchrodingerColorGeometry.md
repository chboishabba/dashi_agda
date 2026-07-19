# Schrödinger colour geometry in DASHI

This lane formalises the structural content of the non-Riemannian colour-space result without promoting unproved empirical claims.

## Formal decomposition

```text
physical spectra / receptor traces
  -> perceptual metric quotient
  -> intrinsic neutral seam
  -> neutral projection + chromatic residual
  -> metric-invariant hue / saturation / lightness coordinates
  -> shortest-path perceptual transport
```

The central theorem surface is not that RGB coordinates are fundamental. It is that an intrinsically characterised neutral axis is preserved by every automorphism of the perceptual metric, and coordinates defined as metric invariants are therefore representation-independent.

## Modules

- `DASHI.Perception.ColorMetricCore`
  - abstract perceptual metric;
  - metric maps and automorphisms;
  - path geometry and selected shortest paths;
  - no Riemannian assumption.
- `DASHI.Perception.NeutralAxisIntrinsic`
  - metric-only characterisation of the neutral axis;
  - proof that metric automorphisms preserve and reflect neutral membership;
  - neutral projection and chromatic residual interface.
- `DASHI.Perception.SchrodingerColorGeometry`
  - intrinsic hue, saturation and lightness carriers;
  - proof that the HSL triple is invariant under metric automorphisms;
  - non-Riemannian shortest-path correction boundary;
  - assembled DASHI bridge.
- `DASHI.Perception.ColorGeometryTests`
  - identity-isometry smoke proofs.

## Promotion boundary

The formalisation does **not** assert that a particular empirical colour metric, neutral-axis definition, or path model satisfies these interfaces. Such a claim requires a concrete model and experimental receipt. The Bezold-Brücke and diminishing-return fields remain candidate-level and are explicitly not universally promoted.

## Next mathematical bridge

A concrete instantiation should provide:

1. the experimentally fitted perceptual metric;
2. its metric-only neutral-axis predicate;
3. a neutral projection or closest-point theorem;
4. shortest paths in the fitted non-Riemannian geometry;
5. an empirical receipt connecting those paths to observed hue shifts and diminishing sensitivity.
