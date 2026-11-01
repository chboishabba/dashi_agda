# Clay Sprint 24 Micro-Lemma Layer

Sprint 24 stops aiming at the full Clay mountain and records the small
formal targets that are now worth proving directly.

## Gate3

Target:

```text
h_pruned(J) <= C / J^alpha
C > 0
alpha > 0
```

Micro-lemma:

```text
PrunedFillDistanceGoesToZero
```

ELI5: if the biggest uncovered gap shrinks like a positive power of `J`, then
eventually every point is close to some retained atom.

Current constants:

```text
alpha = 0.92
C ~= 0.07549
J(0.01) = 9
J(0.001) = 110
J(10^-6) = 200479
```

Still open:

```text
PrunedFillDistanceGoesToZero
PrunedUnionDenseInAngularL2
MoscoRecoveryFromPrunedUnionDensity
Gate3MoscoNoPollutionTransfer
```

## Navier-Stokes

Target:

```text
r * sqrt(2) < 1
```

Micro-lemma:

```text
ResidueDecayBeatsHalfDerivative
```

ELI5: the bad vortex-stretching factor grows like `sqrt(2)` each shell.  If
the residue shrinks by a factor `r` where `r * sqrt(2) < 1`, the bad tail is
summable.

Recorded regimes:

```text
r = 1/3  -> product ~= 0.471, closes strongly
r = 1/2  -> product ~= 0.707, borderline
r = 2/3  -> product ~= 0.943, closes weakly
r = 6/7  -> product ~= 1.212, fails
```

Still open:

```text
BraidResidueControlsPhysicalStretching
DynamicBraidResidueDecayForNS
BraidResidueAbsorbsStretching
```

## Yang-Mills

Target:

```text
beta_true >= 14.16373
rho <= 0.90
```

Micro-lemma:

```text
NonperturbativeCorrectionBudget
```

ELI5: the one-loop curve says where the coupling should be safe.  The real
nonperturbative coupling may deviate from that curve, so the budget tells us
how much error is allowed before the safe margin is lost.

Recorded tolerances:

```text
k = 61 -> eta ~= 0.1048
k = 67 -> eta ~= 0.9180
k = 70 -> eta ~= 1.3247
k = 80 -> eta ~= 2.6802
```

Still open:

```text
NonperturbativeCorrectionBudget
ContinuumUniformRhoBoundAtSafeScale
ContinuumUniformLeakageBound
```

## Lean Disposition

The local `monster/lean-toolchain` and `monster/lakefile.toml` are present,
but `lean` and `lake` were not available on PATH in this sandbox.  No
`ClayThresholds.lean` file was added because it could not be validated without
introducing an unchecked artifact.

Lean micro-lemmas remain port targets:

```text
geometric_tail_summable
one_third_beats_half_derivative
power_law_tends_to_zero
```

## Workers

1. Gate3 power-law limit.
2. Gate3 density/Mosco consumer.
3. NS geometric summability.
4. NS physical residue interface.
5. YM correction-budget implication.
6. Lean toolchain and promotion governance.

All Gate3, Navier-Stokes, Yang-Mills, and Clay promotion flags remain false.
