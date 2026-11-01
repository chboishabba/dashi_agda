# Triadic Exploded-Transform Completion

This tranche completes five theorem targets on top of the merged atomic/exploded-transform bridge.
## Affine algebra
`AffineWarp` provides a forward map, inverse map, and both inverse laws. The module proves identity, composition, and left/right inverse pullback lemmas. Concrete matrix/vector affine implementations can instantiate this extensional record.
## Atomic commutation
Output-support disjointness alone is insufficient because one atom may sample inside the other's support. `StronglyNoninterfering` therefore records output exclusivity plus both source-noninterference conditions. Under that exact hypothesis, `atomic-commutes-under-noninterference` proves pointwise commutation.
## Codec partition address / SSP369 bridge
Codec digits `branch3`, `branch6`, and `branch9` are mapped bijectively to `SSP369Ultrametric.Digit369`. Digit and address round trips, equality reflection, and exact transported-distance preservation are proved at every finite depth.
## Chart-specific MDL descent
`ChartCost` separates side bits and residual bits. `ChartRefinementBound` supplies componentwise nonincrease, and `chart-refinement-implies-mdl-nonincreasing` proves total description-length nonincrease. Strict descent remains an explicit receipt, so admissible refinement is not automatically called beneficial.
## Metric-qualified piecewise-affine approximation
`MetricQualifiedApproximation` requires a partition selector, target map, one local affine candidate per leaf, a distance carrier, tolerance relation, and local pointwise approximation proof. `piecewise-affine-inherits-local-bound` proves the assembled piecewise map satisfies the same pointwise bound globally.
## Consumer surface
`DASHI.Codec.TriadicExplodedTransformCompletion` packages all five lanes into `CompletedExplodedChart` and exports direct consumer theorems for affine round trip, atomic commutation, address round trip, MDL nonincrease, and the metric approximation bound.
## Boundary
This does not assert universal strict MDL descent, continuum density without regularity assumptions, empirical bitrate superiority, or physical closure. Those remain dependent on concrete chart costs, metrics, regularity and empirical receipts.
This tranche completes the five theorem targets requested after the initial
atomic/exploded-transform bridge.
## 1. Affine algebra
`DASHI.Geometry.TriadicExplodedTransformTheorems` defines an extensional
`AffineWarp` with a forward map, inverse map, and both inverse laws. It proves:
- identity pullback;
- composition pullback;
- left inverse pullback;
- right inverse pullback.
Concrete matrix/vector affine implementations can instantiate this record.
The theorem layer does not assume a particular coordinate ring.
## 2. Atomic commutation
Disjoint output support alone is not sufficient for commutation because one
atom may sample from a point transformed by the other. The exact sufficient
condition is `StronglyNoninterfering`, which records:
- exclusive output support;
- the first atom's sampled source lies outside the second support;
- the second atom's sampled source lies outside the first support.
Under this condition, `atomic-commutes-under-noninterference` proves pointwise
commutation.
## 3. Partition-address / SSP369 bridge
The module defines codec partition digits `branch3`, `branch6`, and `branch9`
and total conversions to and from `SSP369Ultrametric.Digit369`.
It proves:
- digit round trips;
- address round trips at every depth;
- equality reflection;
- exact preservation of the transported SSP369 distance.
This gives the codec tree a checked route into the repository's existing
prefix ultrametric rather than merely claiming an analogy.
## 4. Chart-specific MDL descent
`ChartCost` separates side bits from residual bits. A
`ChartRefinementBound` proves that both components are nonincreasing.
The theorem
`chart-refinement-implies-mdl-nonincreasing`
then proves that total description length is nonincreasing by monotonicity of
addition. Strict descent remains an explicit `StrictChartMDLDescent` receipt;
a split is not treated as beneficial merely because it is admissible.
## 5. Metric-qualified piecewise-affine approximation
`MetricQualifiedApproximation` requires:
- a partition selector;
- a target map;
- one local affine candidate per leaf;
- a distance carrier;
- a tolerance relation;
- a pointwise local approximation proof.
`piecewise-affine-inherits-local-bound` proves that the assembled piecewise map
inherits the same pointwise tolerance globally. This is the correct theorem
without pretending that arbitrary discontinuous maps admit uniform affine
approximation under an unspecified metric.
`DASHI.Codec.TriadicExplodedTransformCompletion` packages all five lanes in
`CompletedExplodedChart` and exports direct consumer theorems for:
- affine round trip;
- atomic commutation;
- address round trip;
- MDL nonincrease;
- piecewise metric bound.
The existing canonical SSP trit carrier, SSP369 ultrametric/tree action, causal
chart bridge, and W9 MDL route remain live dependencies.
## Non-promotion boundary
This tranche does not prove:
- that every codec refinement strictly lowers MDL;
- a continuum piecewise-affine density theorem without regularity assumptions;
- an empirical bitrate advantage over AV1;
- physical or analytic closure.
Those require concrete chart costs, metric/regularity hypotheses, and empirical
receipts.
