# Clay Sprint 28 Productive Micro-Lemmas

Sprint 28 records the small advances that can be made without pretending to
solve Clay.

## Gate3

Given:

```text
h_pruned(J) <= C / J^alpha
C = 0.07549
alpha = 0.92 > 0
```

the fill distance tends to zero.  The witness shape is:

```text
J >= ceil((C / epsilon)^(1 / alpha)).
```

Recorded witness table:

```text
epsilon = 10^-2 -> J = 9
epsilon = 10^-3 -> J = 110
epsilon = 10^-4 -> J = 1344
epsilon = 10^-5 -> J = 16410
epsilon = 10^-6 -> J = 200473
```

This closes the ledger-level density micro-lemma:

```text
PowerLawFillDistanceImpliesDensity
```

It does not prove:

```text
PrunedUnionDenseInAngularL2
MoscoRecoveryFromPrunedUnionDensity
Gate3MoscoNoPollutionTransfer
gate3Closed
```

## Navier-Stokes

The exact threshold is:

```text
r * sqrt(2) < 1
```

Recorded products:

```text
r = 1/3 -> 0.471, closes strongly
r = 1/2 -> 0.707, borderline but below critical
r = 2/3 -> 0.943, closes weakly
r = 0.70 -> 0.990, closes barely
r = 6/7 -> 1.212, fails
```

High-shell cutoffs for a one-percent tail:

```text
r = 1/3 -> K0 = 7
r = 1/2 -> K0 = 17
r = 2/3 -> K0 = 127
r = 0.70 -> K0 = 912
```

The productive residue candidate is geometric, not purely combinatorial:

```text
R_K =
  integral chi_K * |omega_K|^2 * lambda_1^+(S_K) * sin^2(theta_K)
  /
  integral |omega_K|^2 * lambda_1^+(S_K) + epsilon
```

The decisive falsification test is:

```text
Q_K <= C * R_K
```

If the dynamic ratio is good but this physical bridge fails, the residue is
symbolic rather than PDE-relevant.

## Yang-Mills

The support-only correction-budget implication is:

```text
beta_true(k) >= beta_one_loop(k) - eta(k)
eta(k) <= beta_one_loop(k) - betaRho090
=> beta_true(k) >= betaRho090
```

with:

```text
betaRho090 = 14.16373
safe diagnostic scale k = 67
```

Selected rho diagnostics:

```text
k = 60  -> rho ~= 0.9055
k = 61  -> rho ~= 0.8815
k = 62  -> rho ~= 0.8582
k = 65  -> rho ~= 0.7918
k = 67  -> rho ~= 0.7504
k = 70  -> rho ~= 0.6924
k = 75  -> rho ~= 0.6054
k = 80  -> rho ~= 0.5294
k = 90  -> rho ~= 0.4048
k = 100 -> rho ~= 0.3095
```

This does not prove:

```text
ContinuumUniformRhoBoundAtSafeScale
ContinuumUniformLeakageBound
Clay Yang-Mills
```

## Boundary

Sprint 28 records ledger-level arithmetic closure and productive test surfaces.
It does not prove Gate3 Mosco/no-pollution, NS `Q_K <= C R_K`, NS dynamic
depletion, YM nonperturbative uniformity, Gate3 closure, Clay Navier-Stokes, or
Clay Yang-Mills.
