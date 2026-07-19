# Exact Galerkin coherence baseline — first non-vacuous result

The first matched N32/N48/N64 run used the same reality-closed positive-transfer
triad at each cutoff, viscosity `nu = 0.01`, target shell `K = 2`, and saved
five states from `t = 0` to `t = 0.001` at each cutoff.

## Cutoff agreement and excursion coverage

The initial packet Gamma was cutoff-independent to floating-point accuracy:

```text
N32  Gamma(0) = 0.7272727272727275
N48  Gamma(0) = 0.7272727272727268
N64  Gamma(0) = 0.7272727272727276
```

It remained above `0.7239` at the last saved state at all three cutoffs. Thus
the `lambda = 0.5` validation was non-vacuous in both training and held-out
sets:

```text
training excursion rows: 10
held-out N64 excursion rows: 5
```

The scalable shell-pair carrier had local shell-pair gross fraction `1.0` on
this deliberately minimal triad experiment.

## What survived

A nonnegative linear combination of the declared pressure, cross-shell,
viscous, and tail features could dominate the sampled

```text
max(A_dot + kappa 1_{Gamma >= lambda}, 0)
```

on the training cutoffs and retained a positive budget margin on held-out N64.
For `lambda = 0.5`, the held-out minimum budget margins were positive for every
sampled `kappa`.

This does not validate the coefficients as analytic constants. The fitted
coefficients were very large and strongly scale-sensitive in the viscous
feature, so this result is only evidence that the finite feature span can fit
the short matched trajectory.

## What was falsified

The first candidate identification

```text
local geometric depletion = max(-A_dot_self_advective, 0)
```

failed decisively. On the dangerous triad, self-packet advection contributed
essentially no negative alignment derivative, while the increase in the smooth
alignment budget came primarily from cross-shell advection. Consequently:

```text
minimum held-out depletion margin for kappa = 0.01: -0.01
minimum held-out depletion margin for kappa = 0.05: -0.05
minimum held-out depletion margin for kappa = 0.10: -0.10
minimum held-out depletion margin for kappa = 0.25: -0.25
```

No tested parameter set therefore satisfied the complete non-vacuous
`danger => local depletion expenditure` gate.

The integrated candidate absorption ratio was also far above one because the
chosen local-depletion denominator was nearly zero:

```text
N32 theta_emp approximately 1.74e17
N48 theta_emp approximately 1.23e18
N64 theta_emp approximately 1.97e17
```

This is a useful falsification, not an implementation failure. It says the
proof currency cannot be the negative self-advective derivative of the chosen
smooth alignment budget.

## Exactness checks

For the declared finite Galerkin system and smooth spectral budget:

- the packet RHS component sum matched the direct projected RHS at machine
  precision;
- the component alignment derivatives matched the direct tangent derivative at
  machine precision;
- the quotient-rule residual was at machine precision;
- the complete analytic tangent derivative passed a central finite-difference
  regression test;
- the hard simple-spectrum pressure formula passed independent eigenvector-sign
  flip tests.

## Revised mathematical fork

The next candidate depletion quantity must be distinct from
`max(-A_dot_self_advective,0)`. The implemented data now support testing at
least these alternatives:

1. the gauge-invariant vorticity-direction turnover magnitude;
2. a projector-distance or spectral-gap-weighted turnover budget;
3. a cumulative cross-shell coherence budget rather than a self-packet budget;
4. a branch-specific quantity conditioned on positive `lambda_2` and
   substantial middle alignment.

The held-out validator deliberately records the failure:

```text
any_budget_coefficient_set_survives_holdout = true
any_nonvacuous_parameter_set_survives_holdout = false
```

Neither field carries theorem, cutoff-uniform, BKM, or Clay authority.
