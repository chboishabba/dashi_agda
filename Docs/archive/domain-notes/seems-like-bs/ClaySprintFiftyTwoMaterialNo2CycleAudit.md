# Clay Sprint 52 Material Source / No-2-Cycle Audit

Sprint 52 is the narrow post-Sprint-51 fork. It checks only:

- whether Sprint 49 advected material parents leave any true-new positive
  source;
- whether Sprint 51 no-2-cycle proxy failures are small in material-packet
  amplitude.

Producer:

```bash
cd ../dashiCFD
python3 scripts/ns_sprint52_material_no2cycle_audit.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint52_material_no2cycle_gpu_audit
```

Replay:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-sprint52-material-no2cycle-summary \
    ../dashiCFD/outputs/sprint52_material_no2cycle_gpu_audit/ns_sprint52_material_no2cycle_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint52_material_no2cycle_gpu_replay
```

Observed six-run N32/N64 result:

- `route_decision = MATERIAL_SOURCE_GATE_CLOSED_NO2CYCLE_AMPLITUDE_BLOCKED`
- `weighted_true_new_material_total = 0`
- `material_true_new_source_absent = true`
- `does_material_source_gate_close = true`
- `no2cycle_proxy_failure_count = 9126`
- `no2cycle_amplitude_small_failure_count = 6993`
- `no2cycle_amplitude_small_failure_fraction = 0.7662721893491125`
- `weighted_no2cycle_amplitude_total = 105041325606418.38`
- `does_no2cycle_amplitude_gate_close = false`

Interpretation:

Sprint 52A closes under current material-parent evidence: the true-new positive
source is absent. Sprint 52B remains blocked: the v1 material-packet amplitude
calibration marks only about 76.6% of proxy-failing cycles as amplitude-small,
below the 90% diagnostic majority threshold.

This is still diagnostic-only. It does not prove theorem-grade physical
oscillation amplitude, weighted amplitude summability, physical bridge, stretch
absorption, no finite-time blowup, or Clay/Navier-Stokes regularity.
