# NS compact-Gamma replenishment absorption

For the bounded transfer potential

```text
B_K = Q_K,+ / (Q_K,+ + 2 nu D_K),
```

the exact Galerkin derivative is split into target nonlinear, off-packet
nonlinear, and viscous contributions.  Define the unsigned mechanism totals

```text
E_K = sum_j max(-B_dot,j, 0),
R_K = sum_j max( B_dot,j, 0).
```

Then

```text
B_dot = R_K - E_K.
```

The empirical target is a strict absorption envelope

```text
R_K <= theta E_K,
theta < 1,
```

on dangerous states.  The script

```text
scripts/ns_compact_gamma_replenishment_audit.py
```

sweeps the same phase/amplitude triad family as the compact-Gamma stress test,
ranks states by `R_K/E_K`, and rechecks the worst cases at N32/N48/N64.

## Formal reduction

`NSCompactGammaReplenishmentAbsorption.agda` proves the integrated algebraic
step.  Given

```text
initial + R = final + E,
R <= thetaE + C,
E = marginE + thetaE,
final >= 0,
```

it derives

```text
marginE <= initial + C.
```

A supplied theorem that dangerous residence consumes `marginE` then yields the
corresponding residence bound.

The remaining PDE work is to construct the split with constants uniform in
shell and cutoff, and to control any remainder `C` through pressure,
commutator, viscosity, and shell/angular tail estimates.

Finite survival of the audit is candidate evidence only.  It does not establish
cutoff-uniformity, BKM continuation, global regularity, or a Clay result.
