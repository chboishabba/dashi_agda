# Clay Sprint 55 YM KP Sum Convergence Correction

Sprint 55 records the corrected KP tail obstruction. The Sprint 54 blocked
contour row at `beta_blocked = 16.7` has a one-step activity ratio below one,
but the KP weighted/combinatorial diameter sum still diverges under the current
`p = 7`, branching `8`, and `c_combo = 8` convention.

Producer:

```bash
python scripts/ym_sprint54_blocked_kp_transfer_table.py \
  --out-dir Docs/Images/clay-analytic-sprint/sprint55_ym_kp_sum_convergence
```

Outputs:

```text
ym_sprint54_blocked_kp_transfer_table.csv
ym_sprint54_blocked_kp_transfer_checks.json
ym_sprint54_blocked_kp_transfer_manifest.json
```

## Corrected Arithmetic

Constants:

```text
p = 7
branching = p + 1 = 8
c_combo = 8
c_min = 0.242
a = 0.5
beta_blocked = 16.7
```

The script convention separates three quantities:

```text
raw contour ratio      = exp(a - beta*c_min)
activity ratio q       = c_combo * raw contour ratio
weighted KP sum ratio  = branching * q
```

At `beta_blocked = 16.7`:

```text
raw contour ratio     = 0.028972736844078417
q                     = 0.23178189475262734
branching * q         = 1.8542551580210187
beta needed for tail  = 19.251582989089552
beta gap              = 2.551582989089553
```

So the geometric ratio gate is not the KP sum gate:

```text
q < 1                 true
branching * q < 1     false
```

## Interpretation

Sprint 55 closes only the accounting ambiguity:

```text
geometricActivityRatioBelowOne
```

is not sufficient for:

```text
AllDiameterKPActivityBound
```

The missing gate is now explicit:

```text
weightedKPSumConvergence
```

Under the current `c_combo = 8` bound, `beta_blocked = 16.7` is insufficient.
The corrected threshold is approximately `19.252`, not `19.1`.

No all-diameter KP certificate, Balaban RG transfer, continuum rho/leakage
bound, OS/Wightman terminal, mass gap, or Clay YM promotion follows.
