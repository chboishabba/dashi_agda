# Clay Sprint 53 No-2-Cycle Physical Amplitude Audit

Sprint 53 tests the remaining Sprint 52 blocker:

- Sprint 52A material true-new source is absent.
- Sprint 52B no-2-cycle amplitude remains blocked under a material-packet
  proxy.
- Sprint 53 recalibrates the failing sign-cycle rows against a shell/time
  net-residue amplitude proxy:
  `N_K(t) = Rplus_K(t) - Rminus_K(t)`.

Producer:

```bash
cd ../dashiCFD
python3 scripts/ns_sprint53_no2cycle_physical_amplitude_audit.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint53_no2cycle_physical_gpu_audit
```

Replay:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-sprint53-no2cycle-physical-summary \
    ../dashiCFD/outputs/sprint53_no2cycle_physical_gpu_audit/ns_sprint53_no2cycle_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint53_no2cycle_physical_gpu_replay
```

Observed six-run N32/N64 result:

- `route_decision = MATERIAL_SOURCE_GATE_CLOSED_PHYSICAL_NO2CYCLE_AMPLITUDE_BLOCKED`
- `weighted_true_new_material_total = 0`
- `material_true_new_source_absent = true`
- `does_material_source_gate_close = true`
- `no2cycle_candidate_count = 12600`
- `no2cycle_proxy_failure_count = 8252`
- `physical_large_cycle_count = 5427`
- `physical_amplitude_small_failure_count = 2825`
- `physical_small_cycle_fraction = 0.3423412506059137`
- `weighted_physical_cycle_amplitude_total = 6.102221992335201e+21`
- `sigma_physical_cycle_fit = -1.1215088689186317`
- `does_physical_cycle_gate_close = false`
- `does_physical_cycle_summability_gate_close = false`

Interpretation:

Sprint 53 does not clear the final NS diagnostic gate. Under the current
material net-residue physical-amplitude proxy, only about 34.2% of
proxy-failing cycles are physically small, and the fitted shell slope is
negative rather than above the half-derivative threshold.

This does not prove the continuum obstruction. The v1 amplitude is computed
from material-parent CSV shell/time residue deltas, not from theorem-grade
`omega dot S omega` truth reconstruction. It is strong diagnostic evidence
that the remaining no-2-cycle blocker is real enough to require either denser
cadence/true physical stretch reconstruction or a pivot away from the current
ternary source-budget route. No Clay/Navier-Stokes promotion follows.
