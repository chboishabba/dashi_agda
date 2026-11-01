# Clay Sprint Fifty Seven Vessel Action Reconciliation

Sprint 57 tests whether the Sprint 56 packet-local accumulated-action ledger
reconstructs the whole-domain vortex-stretching balance.  It compares the
Euclidean `K_cell` packet union against global and covered-mask
`omega dot S omega` action.

## Commands

Producer:

```bash
cd ../dashiCFD
python3 scripts/ns_sprint57_vessel_action_reconciliation_audit.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint57_vessel_action_reconciliation_gpu_audit
```

Replay:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-sprint57-vessel-action-summary \
    ../dashiCFD/outputs/sprint57_vessel_action_reconciliation_gpu_audit/ns_sprint57_vessel_action_reconciliation_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint57_vessel_action_reconciliation_gpu_replay
```

## Observed Batch Result

```text
route_decision = PACKET_ACTION_UNDERCOUNTS_COVERED_STRETCH
time_window_count = 72
packet_local_action_row_count = 3388
global_raw_positive_stretch_action_total = 32075246.214473482
covered_raw_positive_stretch_action_total = 6825780.534479305
packet_raw_positive_stretch_action_total = 1255041.5468506175
global_normalized_positive_action_total = 0.6013179870705523
packet_normalized_positive_action_total = 68.9023403252573
epsilon_raw_positive_vs_covered = -0.8161321565334568
epsilon_raw_positive_vs_global = -0.9608719590659198
epsilon_normalized_positive_vs_global = 113.58553013012235
mean_coverage_fraction = 0.17426474889119467
max_double_count_fraction = 0.0
dangerous_lineage_count = 641
sigma_packet_local_action_fit = -0.4822543927548197
```

## Interpretation

Sprint 57 does not support the simple claim that Sprint 56 failed because
Euclidean packets double-counted positive stretch.  The raw packet ledger
undercounts covered positive stretch by about 81.6% and global positive stretch
by about 96.1%.  At the same time, the normalized packet action is far larger
than normalized global action.

The current obstruction is therefore a normalization/partition mismatch:
packet-local normalized `A+` can look dangerous even though raw packet stretch
does not reconstruct the vessel action.  BT/ultrametric reassignment remains a
valid next hypothesis, but it must preserve raw action and resolve normalized
action inflation rather than merely relabel packets.

## Governance

Sprint 57 is replay evidence only.  It does not prove packet-action
reconstruction, BT reassignment, weighted accumulated-action summability,
physical bridge, stretch absorption, no finite-time blowup, or Clay/NS
promotion.
