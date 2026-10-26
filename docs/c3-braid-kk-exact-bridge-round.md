# C3 continuous braid and Kaluza–Klein gauge max-cut — 2026-10-22

## Checked finite-to-continuous braid result

For the 12-state alternating orbit and phase shifts 0,4,8, consider the **piecewise-linear periodic** paths in the plane, with time parameter T=12. The exact-rational audit computes

```text
min_{t in [0,12], i != j} ||gamma_i(t)-gamma_j(t)||² = 1.
```

Thus the base braid has distance clearance **1**, not just pointwise noncollision. Given a second continuous periodic triple `eta_i` with **uniform Euclidean error** `sup_t ||eta_i(t)-gamma_i(t)|| < 1/2` for every i, the pointwise straight homotopy `H_i(s,t)=(1-s)gamma_i(t)+s eta_i(t)` preserves pairwise distinctness: each relative displacement changes by less than 1 under the homotopy, while the original separation is at least 1. Therefore the closed pure-braid **free isotopy class** is preserved under this explicit sufficient condition. Base-point-preserving based-homotopy requires endpoints be fixed or an explicit identification of basepoints. This is a conditional reconstruction/sampling theorem, not a general statement that ternary quantization preserves braid classes. The finite site chart alone cannot bound observation error.

Reference executable: `scripts/check_c3_ninesite_borromean.py`. The exact fractional minimization works segmentwise on 12 intervals and each of three relative strands.

## KK exact additive connection theorem

`DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda` implements the exact group-theoretic identity

```text
theta = vertical + potential
vertical' = vertical - displacement
potential' = potential + displacement
theta' = theta
```

for any witnessed abelian additive group of one-form coefficients. Physically read `potential = kappa A`, `displacement = kappa dchi`; this is the local invariance of the KK horizontal one-form `dy + kappa A` under a fibre-coordinate change. It is source-written Agda, not kernel certified, and it does not supply differential forms or a 5-dimensional smooth metric by itself.

`scripts/check_kaluza_klein_circle_metric.py` executes a *representative 2+1 block* of the circle-fibre metric `G=[g + phi² k² AAᵀ, phi² kA; phi² kAᵀ, phi²]`, checking exact symbolic coordinate gauge covariance, determinant `det G = phi² det g`, and its block inverse. It does **not** prove the 4+1 Ricci-scalar decomposition, integration over a circle, 4D Einstein/Maxwell field equations, or coupling to observed physical fields.

## Reuse, don't overwrite, recent siblings

PR #1235 (branch `chatgpt/cy-hopf-darkdimension-producer-maxcut`) already has:
- `DASHI/Mathematics/Topology/HopfU1TransitionCocycleExact.agda`: actual U(1) cocycle over phases;
- `DASHI/Mathematics/Topology/HopfU1CurvatureNaturalityExact.agda`: SU(2) Cartan bracket vanishes (not a smooth curvature theorem);
- `DASHI/Mathematics/Topology/HopfU1PrincipalBundleObligationsExact.agda`: principality, smoothness and Chern requirements, not yet all inhabited.

The new KK algebra is deliberately formulated separately because PR #1235 is a sibling branch; promoting its definitions to local authority requires a real merge/import and exact-head check. Any future KK geometric owner must reuse the cocycle, principally smoothness, connection and curvature owners.

PR #1217 owns the Unified physical realization spine; PR #1133 owns native-C3 T9/T18/T27. Neither is by itself a KK Einstein–Maxwell theorem.

## Physical steelman / remaining walls

Strongest supported bridge: `C3-equivariant moving three-body configuration -> pure braid isotopy -> higher-order triple linking`, with proven clearance, plus `U1 algebra -> invariant KK local horizontal form`.

Unpaid:
1. Agda kernel check of both new proof files and repository aggregation.
2. Formal analytic proof of exact clearance and uniform perturbation/relative homotopy, translating the Python exact rational certificate into Agda (or a trusted algebraic kernel with a checked bridge).
3. Full 4+1 principal-circle-bundle connection, gauge-patch consistency, metric gluing and Levi-Civita/Ricci reduction with correct signs/constants.
4. Four-dimensional Einstein–Maxwell plus scalar equations from a specifically dimensioned action and matter sector.
5. A physically derived continuous three-body orbit and empirical/experimental discrimination; merely specifying a periodic orbit is not solving the Newtonian three-body problem.
6. No numerical 3/6/9 motif supplies KK, SU2 or string dimensions without explicit realizing maps.

## Commands

```sh
python3 scripts/check_c3_ninesite_borromean.py
python3 scripts/check_kaluza_klein_circle_metric.py
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3NineSiteAlternatingOrbitExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3NineSiteBalancedChartExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda
```

The Agda commands are specified but **not executed here**. Do not conflate GitHub acceptance with kernel proof.
