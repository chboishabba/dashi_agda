# Jacobian counterexample closure

This package separates exact executable algebra, kernel-visible logical implication, publication status, and historical attribution.

## Exact certificate

`scripts/check_jacobian_noninjective_example.py` uses dependency-free exact rational sparse-polynomial arithmetic to check:

- the displayed three-coordinate map is polynomial;
- its Jacobian determinant reduces identically to `-2`;
- three distinct rational points map to `(-1/4,0,0)`.

The sparse expansion and evaluations remain executable certificates rather than Agda-normalised polynomial proofs.

## Kernel theorem

`DASHI.Algebra.Jacobian.CollisionImpliesNonInjective` proves:

```text
x != y and f x = f y  =>  not Injective f
```

The theorem is exercised definitionally by `CounterexampleRegression.agda` using three distinct constructors with one common image.

## Promotion strata

`InvertibilityStrata.agda` separates:

- derivative nonsingularity;
- local invertibility;
- finite fibres;
- global injectivity;
- global bijectivity;
- polynomial invertibility.

No global inverse is inferred from a local round trip.

`FibreBranching.agda` treats reconstruction as fibre-valued unless a branch, history, and continuity receipt select one source.

## Dimension padding

`DimensionPadding.agda` proves that a collision survives after appending unchanged coordinates. The block-Jacobian determinant preservation remains an explicit receipt, so the higher-dimensional consequence does not require re-expanding every determinant.

The dimension-two lane remains explicitly unresolved.

## Local/global boundary

`LocalGlobalChartBoundary.agda` records that nonsingular local differential structure can coexist with multiple global sheets. Global analysis must track fibre cardinality, branch permutation, behaviour at infinity, and properness.

## Status separation

`ThreeDimensionalCounterexample.agda` distinguishes:

- exact executable checks;
- kernel-proved logical implications;
- stable archival citation;
- peer-reviewed publication;
- historical attribution.

Recent-source and attribution fields remain fail-closed until stable receipts are added. Mathematical consequence is not made dependent on publication status, and publication status is not inferred from the computational certificate.
