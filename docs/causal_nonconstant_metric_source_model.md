# Causal, relational, nonconstant metric/source tranche

This tranche continues the conditional GR/quantum closure ladder with two concrete
advances:

1. a scalar valuation is augmented by typed causal, relational, and orientation
   data so that a finite oriented Lorentzian metric table is selected;
2. the flat model is extended to a nonconstant three-slice warped metric whose
   normalized connection coefficients, compatibility residual, curvature,
   nonzero source, and finite continuity/Bianchi residual are computed by total
   functions.

The result is a checked finite model, not a derivation of continuum spacetime or
a general solution of Einstein's equations.

## 1. Why scalar valuation was insufficient

`DASHI.Geometry.ValuationConformalMetricCandidate` already proves a constructive
underdetermination result: one scalar valuation profile can consume distinct
reference metrics with different causal directions.

`DASHI.Geometry.CausalRelationalMetricSelector` adds the missing data explicitly:

- a valuation profile;
- a causal role for every axis;
- a symmetric pairwise relation table distinguishing the same direction from
  orthogonal directions;
- a spatial orientation retained separately from the metric.

The selector computes

```text
same direction + causal-time role -> negative diagonal entry
same direction + spatial role    -> positive diagonal entry
orthogonal relation              -> zero off-diagonal entry
```

For the canonical `Axis4` frame, the selected table is proved pointwise equal to
the existing balanced-ternary flat metric. The orientation is deliberately not
collapsed into the metric because a Lorentzian metric does not itself encode
handedness.

## 2. Nonconstant local metric

`DASHI.Geometry.NonconstantWarpedLorentzianModel` defines three ordered slices:

```text
past -> present -> future
```

with spatial logarithmic scale depths

```text
0 -> 1 -> 2.
```

The metric signs come from the causal/relational selector, while the spatial
scale is slice-dependent. The model therefore proves that the local metric
actually changes between adjacent slices.

A total comparison function computes the two first differences. Both are the
positive unit coefficient, so the normalized Hubble/log-scale gradient is
nonzero and constant.

## 3. Computed normalized Levi-Civita coefficients

The module classifies symmetric lower-index pairs and computes the finite
FLRW-like coefficient table from the metric gradient. In particular,

```text
Gamma^0_ii = H
Gamma^i_0i = Gamma^i_i0 = H
```

for each spatial direction in the normalized frame. Lower-index symmetry is
proved from the symmetric pair classifier rather than inserted as a Boolean.
At least one coefficient is proved nonzero.

This is a finite normalized Christoffel table. It is not a proof of the smooth
Levi-Civita theorem for arbitrary metrics.

## 4. Computed metric compatibility residual

`DASHI.Geometry.NonconstantWarpedMetricCompatibility` compares the spatial
metric log-gradient with the corresponding computed connection coefficient.
For every checked edge and spatial axis it evaluates

```text
metric gradient - connection gradient = 0.
```

The residual is computed from the same total signed-difference function used by
the geometry model. This is a finite normalized `nabla g` check, not the general
smooth metric-compatibility identity.

## 5. Computed curvature

The discrete derivative of the Hubble/log-scale coefficient is computed to be
zero, while its square is positive. The resulting warped sectional-curvature
carrier is therefore computed to be nonzero.

This is the finite constant-H analogue of the curvature contribution that
remains when `H-dot = 0` but `H^2` is nonzero.

## 6. Nonzero action-derived matter source

`DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel` maps the computed
positive curvature to a reduced de-Sitter-like Einstein tensor:

- positive time-time density;
- equal negative spatial pressure;
- zero off-diagonal entries.

A separate total matter-action variation computes the source tensor. The
Einstein and matter tensors are then proved pointwise equal. This preserves the
repository's required route

```text
defect/coupling -> matter action -> metric variation -> stress tensor
```

rather than adding a direct `defect energy -> T_mu_nu` coercion.

## 7. Computed finite Bianchi/continuity residual

The source obeys the exact finite equation of state

```text
rho + p = 0.
```

Its density is constant across the checked slices. Consequently the finite
continuity residual

```text
delta rho + H (rho + p)
```

reduces by computation to zero. This is the model's contracted-Bianchi/
continuity receipt. It is not the general differential Bianchi identity.

## 8. Regression surface

`DASHI.Physics.Closure.CausalNonconstantGeometryRegression` checks:

- causal metric selection;
- pointwise agreement with the canonical flat sign table;
- actual metric-scale change;
- nonzero computed connection coefficient;
- lower-index symmetry;
- zero computed metric-compatibility residual;
- nonzero computed curvature;
- nonzero matter source;
- pointwise Einstein/source equality;
- zero finite continuity/Bianchi residual;
- continued blocking of residue-energy/gravitational-mass identification.

## Remaining obligations

The next proof-producing steps remain:

1. replace the finite slice set with a controlled lattice family and prove a
   continuum or convergence theorem;
2. derive the causal/orientation/relational selector from the kernel/lift tower
   rather than supplying the canonical frame;
3. compute the full discrete Riemann, Ricci, scalar, and Einstein contractions,
   including inverse-metric and normalization factors;
4. prove a genuine discrete Bianchi identity from curvature symmetries and then
   transport it to a continuum theorem;
5. derive a nonzero matter action from a physical residue carrier and validate
   its Newtonian and relativistic limits;
6. retain the existing mass, quantum-GR, and theory-of-everything promotion
   gates until those mathematical and empirical obligations are discharged.
