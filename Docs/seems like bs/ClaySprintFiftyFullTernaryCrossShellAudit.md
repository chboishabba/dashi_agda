# Clay Sprint 50 Full Ternary Cross-Shell Audit

Sprint 50 adds an audit layer on top of Sprint 49 material-parent artifacts.
It does not rerun GPU truth, packet matching, or N64 shell diagnostics.

`dashiCFD` consumes Sprint 49 output directories containing:

- `ns_material_parent_table.csv`
- `ns_material_parent_summary.json`

and writes:

- `ns_full_ternary_transition_matrix.csv`
- `ns_cross_shell_source_decomposition.csv`
- `ns_ternary_cross_shell_summary.json`

The producer derives transitions from `parent_state -> child_state`, not from
Sprint 49 `classification`. Source kind is derived from `parent_relation` and
`abs(K_child - K_parent)`. The BT-distance field is only
`BT_distance_proxy = abs(K_child - K_parent)`, a diagnostic proxy rather than a
theorem-grade BT metric.

Producer command:

```bash
python3 scripts/ns_ternary_cross_shell_matrix.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint50_full_ternary_cross_shell_gpu_audit
```

`dashi_agda` replays the summary JSON and optional sibling CSVs with:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-ternary-cross-shell-summary \
    ../dashiCFD/outputs/sprint50_full_ternary_cross_shell_gpu_audit/ns_ternary_cross_shell_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint50_full_ternary_cross_shell_gpu_replay
```

## Observed Batch Result

The current six-run N32/N64 GPU batch routes as:

- `route_decision = CROSS_PLUS_FROM_MINUS_DOMINATES`
- `dominant_red_source_state = minus`
- `dominant_red_source_kind = cross_shell`
- `weighted_cross_plus_from_minus = 93419828142802.9`
- `weighted_cross_plus_from_zero = 0`
- `weighted_cross_plus_from_plus = 63297126901733.78`
- `sigma_cross_from_minus = 0.5961054317081029`
- `sigma_cross_from_zero = 0`
- `sigma_cross_from_plus = 0.403894568291897`

Interpretation: Sprint 49 moved the pressure away from true-new red material.
Sprint 50 further localizes the observed cross-shell plus source: in the
current batch, minus-to-plus cross-shell ancestry dominates zero-to-plus and
plus-to-plus cross-shell ancestry.

This remains diagnostic-only. The adjacent-only packet theorem is insufficient,
cross-shell summability is unproved, BT-distance decay is only a candidate, and
all Clay/Navier-Stokes promotion flags remain false.

The Agda receipt is
`DASHI.Physics.Closure.ClaySprintFiftyFullTernaryCrossShellAuditReceipt`.
