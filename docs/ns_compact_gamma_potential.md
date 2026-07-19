# NS compact-Gamma potential lane

The bounded soft-alignment potential was falsified on the matched dangerous
triad: direction and projector path lengths were large, but signed escape from
the potential was zero.  The next bounded observable is tied directly to the
transfer ratio itself.

## Potential

Let

```text
Q_K = signed target-packet nonlinear transfer,
D_K = target-packet Fourier dissipation,
V_K = 2 nu D_K,
Gamma_K = Q_K,+ / V_K.
```

Define

```text
B_K = Q_K,+ / (Q_K,+ + V_K)
    = Gamma_K / (1 + Gamma_K).
```

Then `0 <= B_K < 1`, and for every `lambda >= 0`,

```text
Gamma_K >= lambda
iff
B_K >= lambda / (1 + lambda).
```

This makes the dangerous set an exact level set of a bounded potential rather
than a geometric proxy.

## Exact finite-Galerkin derivative

On the strict positive-transfer branch, the audit computes exact tangent
derivatives of

```text
Q_K,
D_K,
V_K,
Gamma_K,
B_K.
```

The nonlinear derivative uses

```text
N'(u)[v]
  = -P[(v . grad)u + (u . grad)v].
```

The full Galerkin tangent is partitioned into:

```text
target advective,
target pressure,
off-packet advective,
off-packet pressure,
target viscous,
off-packet viscous.
```

Each contribution is propagated linearly through `Q_dot`, `D_dot`, and
`B_dot`, with component-sum residual checks.  A central directional finite
difference independently checks the direct derivative.

At `Q_K = 0`, the positive part is not classically differentiable.  The audit
marks that branch unresolved and excludes it from signed-escape validation.

## One-sided residence currency

In parabolic time `tau = nu 2^(2K) t`, define

```text
compact depletion     = max(-dB_K/dtau, 0),
compact replenishment = max( dB_K/dtau, 0).
```

The matched-cutoff audit tests whether dangerous Gamma forces a positive compact
escape cost and verifies the bounded-potential accounting

```text
integral depletion
  <= B_K(t0) + integral replenishment + quadrature allowance.
```

It also identifies whether target nonlinearity, off-packet nonlinearity, or
viscosity supplies the signed escape.

## Agda surface

`DASHI/Physics/Closure/NSCompactGammaPotentialDerivative.agda` instantiates the
existing division-free quotient rule with

```text
Q = B T,
T = Q + V,
Q' = B' T + B T'.
```

It also adapts a future danger-to-compact-escape proof into the already checked
bounded-potential residence theorem.

## Frontier

A positive finite result would leave the replenishment estimate

```text
integral G_K <= theta integral D_K + C,
theta < 1,
```

and cutoff-uniform passage.  A negative result would falsify compact Gamma as a
one-sided depletion potential even though it exactly parameterizes the danger
set.

No finite experiment in this lane carries BKM, global-regularity, or Clay
authority.
