# Clay Sprint 49 Material Parent Replay

Sprint 49 separates heavy material-parent matching from lightweight Agda
replay.

`dashiCFD` owns the GPU-produced parent artifacts:

- `ns_material_parent_table.csv`
- `ns_material_parent_summary.csv`
- `ns_material_parent_summary.json`

`dashi_agda` consumes `ns_material_parent_summary.csv` with:

```bash
python scripts/ns_diagnostic_harness.py \
  --replay-material-parent-summary ns_material_parent_summary.csv \
  --out-dir Docs/Images/clay-analytic-sprint/sprint49_material_parent_N64_seed0
```

The replay writes:

- `ns_material_parent_summary.csv`
- `ns_material_parent_summary.json`
- `ns_diagnostic_checks.json`
- `ns_diagnostic_manifest.json`

The replay reports:

- `sigma_true_new`
- `sigma_tracking_uncertain`
- `sigma_cross_shell`
- `sigma_low_shell`
- `sigma_total_material`

## GPU Batch Result

Current Sprint 49 GPU batch artifacts:

- `../dashiCFD/outputs/sprint49_material_parent_N32_seed0_gpu/`
- `../dashiCFD/outputs/sprint49_material_parent_N32_seed1_gpu/`
- `../dashiCFD/outputs/sprint49_material_parent_N64_seed0_gpu/`
- `../dashiCFD/outputs/sprint49_material_parent_N64_seed1_gpu/`
- `../dashiCFD/outputs/sprint49_material_parent_gpu_batch/`

All four N32/N64 seed0/seed1 GPU runs replay as
`ADJACENT_PACKET_THEOREM_INSUFFICIENT`.

Observed split:

- `weighted_true_new = 0` in all four runs.
- `sigma_true_new = 0` in all four runs.
- Tracking uncertainty is zero or small; max observed
  `sigma_tracking_uncertain = 0.031127499228515876`.
- Weighted cross-shell source dominates weighted low-shell and tracking source.

Interpretation: Sprint 49 does not currently kill the residue route by true-new
positive material creation. It moves the immediate analytic pressure to an
adjacent/cross-shell packet theorem.

Route status is diagnostic-only:

- `MATERIAL_PARENT_REPAIRS_NEW_SOURCE_DIAGNOSTIC_ONLY`
- `TRUE_NEW_SOURCE_SUBCRITICAL`
- `TRACKING_UNCERTAIN_NEEDS_DENSER_SNAPSHOTS`
- `ADJACENT_PACKET_THEOREM_INSUFFICIENT`

The replay does not load N64 truth snapshots, rerun CPU shell diagnostics,
rerun packet matching, prove source summability, prove the physical bridge,
prove stretch absorption, prove no finite-time blowup, or promote Clay
Navier-Stokes regularity.

The Agda receipt is
`DASHI.Physics.Closure.ClaySprintFortyNineMaterialParentReplayReceipt`.
All Clay, Navier-Stokes, and terminal promotion flags remain false.
