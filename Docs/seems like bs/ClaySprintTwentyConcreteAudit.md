# Clay Sprint 20 Concrete Audit

Sprint 20 records the concrete calculation tables behind the Sprint 19 audit
targets.  These are target-sharpening calculations, not proofs of the open
lemmas.

## Gate3

For the model law:

```text
h_J <= pi / (38 J)
```

the sufficient witnesses are:

| target | sufficient J |
| ---: | ---: |
| `h_J < 0.10` | 1 |
| `h_J < 0.05` | 2 |
| `h_J < 0.02` | 5 |
| `h_J < 0.01` | 9 |
| `h_J < 0.005` | 17 |
| `h_J < 0.001` | 83 |
| `h_J < 0.0001` | 827 |
| `h_J < 10^-6` | 82674 |

The live theorem remains:

```text
PruningPreservesCumulativeFillDistance:
  exists C alpha,
    alpha > 0 and h_pruned(J) <= C / J^alpha
```

The table does not prove Mosco recovery.

## Navier-Stokes

The conditional braid proof closes exactly when:

```text
r * sqrt(2) < 1
```

Recorded products:

| r | `r * sqrt(2)` | closes? |
| ---: | ---: | --- |
| `1/3` | 0.471 | yes |
| `1/2` | 0.707 | critical-ish |
| `2/3` | 0.943 | yes, weak |
| `1/sqrt(2)` | 1.000 | no margin |
| `3/4` | 1.061 | no |
| `6/7` | 1.212 | no |
| `0.9` | 1.273 | no |
| `1.0` | 1.414 | no |

At `K = 20`, the `(6/7)` regime has factor about `46.92`; coherent tubes
have factor `1024`.  This makes the current NS test concrete:

```text
R_K = unbalanced expansive transitions / admissible transitions
check R_(K+1) / R_K < 1/sqrt(2)
```

This only matters after `BraidResidueControlsPhysicalStretching` is proved.

## Yang-Mills

For the usable target:

```text
rho <= 0.90
beta >= 14.16373
```

the one-loop diagnostic budget is:

| k | beta_one_loop | budget |
| ---: | ---: | ---: |
| 50 | 12.7774 | shortfall 1.3863 |
| 55 | 13.4552 | shortfall 0.7085 |
| 60 | 14.1329 | shortfall 0.0308 |
| 61 | 14.2685 | tolerance 0.1048 |
| 67 | 15.0818 | tolerance 0.9180 |
| 70 | 15.4884 | tolerance 1.3247 |

The practical target is:

```text
ContinuumUniformRhoBoundAtSafeScale:
  exists k0 >= 67 such that rho(beta_true(k0,a0)) <= 0.90
```

plus `ContinuumUniformLeakageBound` and a genuine
`NonperturbativeCorrectionBound`.

All Gate3, Navier-Stokes, Yang-Mills, and Clay promotion flags remain false.

