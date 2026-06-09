# Clay Sprint 31 Algebraic Micro-Closures

Sprint 31 records the small algebraic closures unlocked by the ternary residue
refinement.  These are bookkeeping and threshold results only.  They do not
prove the analytic PDE or constructive QFT gates.

## Closed Ternary Algebra

Trit partition:

```text
negativePart tau + neutralPart tau + positivePart tau = 1
```

Ternary mass conservation:

```text
B_K^- + B_K^0 + B_K^+ = P_K
```

Residue bounds:

```text
0 <= R_K^- <= 1
0 <= R_K^0 <= 1
0 <= R_K^+ <= 1
```

Net residue bounds:

```text
-1 <= R_K^+ - R_K^- <= 1
```

These are algebraic consequences of the ternary partition and nonnegative
weights.  They do not prove that `R_K^+` controls physical vortex stretching.

## Closed Tail Algebra

If:

```text
R^+_(K+1) <= r * R^+_K
r * sqrt(2) < 1
```

then the high-shell tail is geometric:

```text
sum_{K >= K0} (r * sqrt(2))^K
  = (r * sqrt(2))^K0 / (1 - r * sqrt(2))
```

This closes only the summability arithmetic.  It does not prove deterministic
decay for actual Navier-Stokes trajectories.

## Gate3 Power Law

The pruned fill-distance power law still gives limit zero:

```text
C = 0.07549
alpha = 0.92
J(epsilon) = ceil((C / epsilon)^(1 / alpha))
```

Witnesses:

```text
1e-2 -> 9
1e-3 -> 110
1e-4 -> 1344
1e-5 -> 16410
1e-6 -> 200473
1e-8 -> 29920357
```

Mosco recovery and no-pollution remain open.

## YM Correction Budget

The correction-budget implication is algebra:

```text
beta_true k >= beta_oneLoop k - eta k
eta k <= beta_oneLoop k - betaRho090
=> beta_true k >= betaRho090
```

The new diagnostic row:

```text
k = 120
beta_oneLoop = 22.26586
etaMax = 8.10213
rhoDiagnostic = 0.1809
```

The nonperturbative correction bound, continuum-uniform rho bound, and leakage
bound remain open.

## Boundary

This sprint records algebraic micro-closures only.  It does not prove
`Q_K <= C R_K^+`, prove `R^+` decay for actual Navier-Stokes, prove pressure
decorrelation, close Gate3 Mosco/no-pollution, prove Yang-Mills
nonperturbative uniformity, perform Lean-port work, or promote any Clay claim.
Uploaded notes, preliminary computations, external artifacts, and tool outputs
are context only, not Agda authority or promotion evidence.
