# NS bounded-turnover potential lane

The matched dangerous-triad experiment found large vorticity-direction and
smooth spectral-projector path-length rates.  Those rates are useful geometric
observables, but path length is not itself a finite budget: a direction may
rotate repeatedly without exhausting any bounded quantity.

This lane replaces the unsigned question

```text
is turnover large during dangerous Gamma?
```

with the sharper one-sided question

```text
does dangerous Gamma force signed escape from a bounded potential?
```

## Bounded potential

The finite-Galerkin potential is

```text
A_K = < omega_K^T P_beta(S_K) omega_K > / < |omega_K|^2 >,
P_beta(S) = exp(beta S) / trace(exp(beta S)).
```

Since `P_beta` is positive semidefinite with trace one,

```text
0 <= A_K <= 1.
```

For each exact Galerkin tangent, the audit derives

```text
A_dot
  = direction_motion
  + projector_motion
  + enstrophy_weight_redistribution.
```

The terms are

```text
direction_motion
  = < |omega|^2 2 xi_dot . P_beta xi > / E,

projector_motion
  = < |omega|^2 xi . P_beta_dot xi > / E,

weight_redistribution
  = < (|omega|^2)_dot (a - A) > / E.
```

Their sum is checked against the quotient derivative computed from the exact
numerator and enstrophy tangents.

## One-sided accounting

Define

```text
D = max(-A_dot, 0)
G = max( A_dot, 0).
```

Then

```text
A_dot = G - D.
```

Integration gives

```text
A(t0) + integral G = A(t1) + integral D,
```

and `A(t1) >= 0` yields

```text
integral D <= A(t0) + integral G.
```

Saved-checkpoint trapezoids include an explicit quadrature allowance rather than
claiming exact continuum integration.

The structural implication is proved in

```text
DASHI/Physics/Closure/NSBoundedPotentialTurnoverBudget.agda
```

including the composition

```text
danger cost * dangerous residence <= signed depletion
signed depletion <= initial potential + replenishment
------------------------------------------------------
danger cost * dangerous residence <= initial potential + replenishment.
```

## What the audit distinguishes

`scripts/ns_bounded_turnover_potential_audit.py` reports:

- unsigned direction and projector path-length rates;
- signed direction, projector, and redistribution contributions;
- net alignment escape and replenishment;
- productive escape divided by path length;
- exact tangent-decomposition residuals;
- interval one-sided balance residuals;
- bounded-potential margins with quadrature allowance;
- non-vacuous held-out danger-to-signed-escape tests across N32/N48/N64.

A large unsigned turnover rate can coexist with zero signed escape.  The test
suite includes an isotropic-projector example where the vorticity direction
moves but the bounded alignment potential stays exactly constant.

## Remaining frontier

A successful route now requires both:

```text
Gamma_K >= lambda  ->  D_K >= c_lambda
```

and an analytic estimate controlling replenishment by pressure, viscosity,
commutators, and shell/angular tails:

```text
integral G_K <= theta integral D_K + C,
with theta < 1 and C uniform in K.
```

The finite audit can rank and falsify candidate signed mechanisms.  It does not
supply cutoff-uniform compactness, BKM continuation, or global regularity.
