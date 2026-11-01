# Clay Sprint Fifty Eight Normalized Action Inflation

Sprint 58 follows Sprint 57's vessel/action reconciliation result.  It tests
the exact algebraic mismatch:

```text
sum_P max((stretch_P / enstrophy_P) dt, 0)
```

versus:

```text
max((sum_P stretch_P / sum_P enstrophy_P) dt, 0)
```

The first quantity is the Sprint 56 packet-local normalized ledger.  The second
is the covered/global ratio-of-sums ledger.  These are not additive in general.

## Commands

Producer:

```bash
cd ../dashiCFD
python3 scripts/ns_sprint58_normalized_action_inflation_audit.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint58_normalized_action_inflation_gpu_audit
```

Replay:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-sprint58-normalized-action-inflation-summary \
    ../dashiCFD/outputs/sprint58_normalized_action_inflation_gpu_audit/ns_sprint58_normalized_action_inflation_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint58_normalized_action_inflation_gpu_replay
```

## Observed Batch Result

```text
route_decision = NORMALIZED_ACTION_NONADDITIVE_RATIO_INFLATION
time_window_count = 72
packet_inflation_row_count = 29448
packet_normalized_positive_action_total = 68.9023403252573
covered_ratio_positive_action_total = 0.014049241013601263
global_ratio_positive_action_total = 0.006006227279589505
sum_ratios_over_ratio_of_sums_covered = 4904.346096600663
sum_ratios_over_ratio_of_sums_global = 11471.817018880183
low_enstrophy_denominator_fraction = 0.012394729693018202
inflation_candidate_fraction = 0.3526215702254822
```

## Interpretation

The Sprint 56 normalized packet ledger is inflated primarily because it sums
local normalized ratios.  It is not mostly explained by a large population of
low-enstrophy packet denominators: only about `1.24%` of packet rows meet the
configured low-denominator threshold.  The ratio inflation is structural:
`sum(stretch_P / enstrophy_P)` is not the same object as
`sum(stretch_P) / sum(enstrophy_P)`.

The current NS route cannot use the Sprint 56 packet-local normalized `A+`
sum as a vessel-additive source without a new theorem controlling this
non-additive ratio inflation.  A raw-action or energy-weighted normalized
ledger is the next safer object.

## Governance

Sprint 58 is diagnostic evidence only.  It does not prove normalized-action
additivity, denominator control, packet-action reconstruction, weighted
summability, physical bridge, stretch absorption, no finite-time blowup, or
Clay/NS promotion.
