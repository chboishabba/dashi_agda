# Clay Sprint 21 Frontier Audit

Sprint 21 records the next frontier result after the Sprint 20 tables.

## Gate3

The pruned fill-distance audit is recorded with exponent:

```text
alpha = 0.92 > 0
```

ELI5: the remaining dots still cover the circle.  The gaps shrink like a
positive power of the number of levels.  The pruning costs some rate, but it
does not kill density.

This closes the density side as a support result.  It does not close the
Gate3 flag.  The remaining Gate3 obligations are:

```text
MoscoRecoveryFromPrunedUnionDensity
Gate3MoscoNoPollutionTransfer
MassShellBridgeCalibration
```

## Navier-Stokes

The useful threshold is still:

```text
r * sqrt(2) < 1
```

DNS-like `r = 2/3` closes the conditional arithmetic because
`(2/3) * sqrt(2) ~= 0.943`.  BT-only `r = 6/7` fails because
`(6/7) * sqrt(2) ~= 1.212`.

ELI5: the bad stretching grows like `sqrt(2)` per level.  Any real dynamics
that shrinks the bad residue faster than `1/sqrt(2)` wins.  The repo still
does not prove real Navier-Stokes does that.

The hard NS gates remain:

```text
BraidResidueControlsPhysicalStretching
DynamicBraidResidueDecayForNS below the critical ratio
CoherentTubeExclusion
```

## Yang-Mills

The usable contraction target remains:

```text
rho <= 0.90
beta >= 14.1637
```

The diagnostic one-loop safe scale is recorded as:

```text
k0 = 61
eta_0.90(61) ~= 0.1048
eta_0.90(67) ~= 0.9180
eta_0.90(70) ~= 1.3247
```

ELI5: the toy forecast is only safe after about 61 steps, and the later you
start, the more error the real proof may tolerate.  This is an error budget,
not a Balaban proof.

The hard YM gates remain:

```text
NonperturbativeCorrectionBound
ContinuumUniformRhoBoundAtSafeScale
ContinuumUniformLeakageBound
ConstructiveQFTTerminals
```

## Six Workers

1. Gate3 Mosco recovery typing.
2. Gate3 mass-shell bridge calibration.
3. NS analytic residue functional.
4. NS physical stretching control plus dynamic ratio test.
5. YM nonperturbative correction/rho/leakage bound.
6. Governance and promotion audit.

All promotion flags remain false.
