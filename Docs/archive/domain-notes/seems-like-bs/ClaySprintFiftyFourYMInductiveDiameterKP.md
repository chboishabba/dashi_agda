# Clay Sprint 54 YM Inductive Diameter KP Target

Sprint 54 turns the Sprint 53 YM result into an explicit bare-vs-blocked scale
diagnostic and records the next theorem target.

Producer:

```bash
python scripts/ym_sprint54_blocked_kp_transfer_table.py \
  --out-dir Docs/Images/clay-analytic-sprint/sprint54_ym_blocked_kp_transfer
```

Outputs:

```text
ym_sprint54_blocked_kp_transfer_table.csv
ym_sprint54_blocked_kp_transfer_checks.json
ym_sprint54_blocked_kp_transfer_manifest.json
```

## Result

Constants:

```text
p = 7
BT branching factor = 8
c_min = 0.242
a = 0.5
beta_bare = 6.0
```

Selected rows:

| label | beta blocked | literal blocked KP | suppressive unit KP | blocked contour KP | ratio d2/d1 | status |
|---|---:|---:|---:|---:|---:|---|
| physical_bare | 6.0 | 7.980170 | 0.019830 | 3.087747 | 0.385968 | fails |
| one_loop_carrier | 7.69 | 7.996341 | 0.003659 | 2.051275 | 0.256409 | fails |
| kp_threshold | 10.13 | 7.999681 | 0.000319 | 1.136532 | 0.142067 | fails p+1 |
| strict_seed | 13.64 | 7.999990 | 0.00000953 | 0.486053 | 0.060757 | blocked contour clears |
| rg_flowed_carrier | 16.7 | 7.99999955 | 0.000000447 | 0.231782 | 0.028973 | blocked contour clears |

Summary:

```text
literal bare rows passing = 0
literal blocked rows passing = 0
blocked contour rows passing = 2
rows requiring Balaban RG transfer = 2
proof gate = false
```

## Interpretation

The Sprint 54 table makes the exact YM gap explicit:

```text
The literal Wilson-defect activity does not supply KP suppression.
The blocked contour/action envelope supplies finite-prefix suppression at
beta = 13.64 and beta = 16.7.
Using that envelope for physical YM requires BalabanRGScaleTransfer.
```

The next mathematical target is only the first part of the all-diameter story:

```text
geometricRatioUniform:
  z(d+1) <= q * z(d), q < 1
```

If that is proved for the blocked contour/action activity, it supplies a
geometric activity envelope. It does not by itself prove the KP
weighted/combinatorial diameter sum. A separate certificate must show:

```text
weightedKPSumConvergence:
  sum_d incompatibility_count(d) * z(d) < threshold
```

Only after that weighted tail certificate can the repo consume the envelope as
`AllDiameterKPActivityBound`. That still does not promote YM until Balaban RG
scale transfer justifies replacing the physical bare activity at beta `6.0` by
the blocked carrier-scale activity.

## Dependency

```text
geometricRatioUniform + qBelowOne
  -> weightedKPSumConvergence
  -> AllDiameterKPActivityBound
  -> BalabanRGScaleTransfer
  -> ContinuumUniformRhoBound
  -> ContinuumUniformLeakageBound
  -> OS/Wightman and mass gap
```

All downstream gates remain open in this sprint.
