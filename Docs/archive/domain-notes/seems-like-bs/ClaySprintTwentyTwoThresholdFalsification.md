# Clay Sprint 22 Threshold / Falsification Audit

Sprint 22 records the next useful calculations without promoting Clay.

## Gate3

The pruned fill-distance law is now recorded in the power-law form:

```text
h_pruned(J) <= C / J^alpha
alpha = 0.92
C ~= 0.07549
```

The constant is anchored at the observed point `h(9) ~= 0.01`.

Witnesses:

| target | sufficient J |
| ---: | ---: |
| `0.01` | `9` |
| `0.001` | `110` |
| `0.0001` | `1344` |
| `10^-6` | `200479` |

Positive alpha is enough for density if the actual pruned bound is proved.
It is not a Mosco proof. The open gates remain:

```text
PruningPreservesCumulativeFillDistancePowerLaw
MoscoRecoveryFromPrunedUnionDensity
Gate3MoscoNoPollutionTransfer
```

## Navier-Stokes

The braid-residue criterion is still:

```text
r * sqrt(2) < 1
```

Tail-depth thresholds:

| r | closes? | K0 for tail < 10^-2 | K0 for tail < 10^-6 |
| ---: | ---: | ---: | ---: |
| `1/3` | yes | `7` | `20` |
| `1/2` | yes | `17` | `44` |
| `2/3` | yes, weak | `127` | `284` |
| `0.70` | yes, extremely weak | `912` | `1824` |
| `1/sqrt(2)` | no margin | never | never |
| `0.75` | no | diverges | diverges |
| `6/7` | no | diverges | diverges |
| `0.90` | no | diverges | diverges |
| `1.00` | no | diverges | diverges |

The static Leray/Sobolev route remains killed by the scaling counterfamily.
The live Clay-facing gates remain:

```text
BraidResidueControlsPhysicalStretching
DynamicBraidResidueDecayForNS below r < 1/sqrt(2)
CoherentTubeExclusion
```

## Yang-Mills

The usable target remains:

```text
rho <= 0.90
beta_true >= 14.16373
```

Using the one-loop diagnostic:

```text
beta_one_loop(k) = 6 + 0.1355488 k
eta_k = beta_one_loop(k) - 14.16373
```

Tolerance table:

| k | beta_one_loop | tolerance |
| ---: | ---: | ---: |
| `60` | `14.1329` | shortfall `0.0308` |
| `61` | `14.2685` | `0.1048` |
| `62` | `14.4040` | `0.2403` |
| `65` | `14.8107` | `0.6469` |
| `67` | `15.0818` | `0.9180` |
| `70` | `15.4884` | `1.3247` |
| `75` | `16.1662` | `2.0024` |
| `80` | `16.8439` | `2.6802` |
| `90` | `18.1994` | `4.0357` |
| `100` | `19.5549` | `5.3911` |

The practical YM audit target is:

```text
NonperturbativeCorrectionBound at k0 >= 67
ContinuumUniformRhoBoundAtSafeScale
ContinuumUniformLeakageBound
```

This is still a Balaban/constructive-QFT problem, not a one-loop proof.

## T7A Quarantine

The T7A correction is recorded as bookkeeping only:

```text
beta*_T7A ~= 16.5556
small-depth c7(d) > 7^d for d <= 3
crossover at d >= 4
T7A does not promote Yang-Mills
```

It remains worse than the current usable `rho <= 0.90` target and does not
replace continuum-uniform nonperturbative control.

## Workers

1. Gate3 pruned power law and Mosco recovery.
2. NS tail threshold and ratio audit.
3. NS physical stretching bridge.
4. YM safe-scale correction budget.
5. T7A quarantine and KP governance.
6. Integration, validation, and promotion audit.

All Gate3, Navier-Stokes, and Yang-Mills promotion flags remain false.
