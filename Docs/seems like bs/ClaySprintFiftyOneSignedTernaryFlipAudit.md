# Clay Sprint 51 Signed Ternary Flip Audit

Sprint 51 rereads the Sprint 50 `minus -> plus` cross-shell source through the
ternary involution: minus and plus are paired states, so the relevant
diagnostic object is signed flip imbalance, not raw plus replenishment alone.

The `dashiCFD` producer consumes Sprint 49 material-parent artifacts and writes:

- `ns_cross_shell_flip_balance.csv`
- `ns_net_ternary_lyapunov.csv`
- `ns_bt_signed_flip_decay.csv`
- `ns_no2cycle_diagnostic.csv`
- `ns_signed_ternary_flip_summary.json`

Run:

```bash
cd ../dashiCFD
python3 scripts/ns_signed_ternary_flip_audit.py \
  --inputs \
    outputs/sprint49_material_parent_N32_seed0_gpu \
    outputs/sprint49_material_parent_N32_seed1_gpu \
    outputs/sprint49_material_parent_N32_seed2_gpu \
    outputs/sprint49_material_parent_N32_seed3_gpu \
    outputs/sprint49_material_parent_N64_seed0_gpu \
    outputs/sprint49_material_parent_N64_seed1_gpu \
  --out-dir outputs/sprint51_signed_ternary_flip_gpu_audit
```

Replay:

```bash
python3 scripts/ns_diagnostic_harness.py \
  --replay-signed-ternary-flip-summary \
    ../dashiCFD/outputs/sprint51_signed_ternary_flip_gpu_audit/ns_signed_ternary_flip_summary.json \
  --out-dir Docs/Images/clay-analytic-sprint/sprint51_signed_ternary_flip_gpu_replay
```

Observed six-run N32/N64 GPU batch:

- `route_decision = NO2CYCLE_FAILS`
- `weighted_cross_minus_to_plus = 93419828142802.9`
- `weighted_cross_plus_to_minus = 84731761817324.95`
- `absolute_flip_imbalance = 8688066325477.953`
- `signed_flip_imbalance_fraction_of_paired_flow = 0.048767829281919015`
- `does_signed_flip_balance = true`
- `eta_signed_flip_by_p = 0.9693578219106342`
- `does_signed_flip_decay = true`
- `q_net_residue_times_sqrt2 = 201.0699673756105`
- `does_net_residue_decay = false`
- `no2cycle_candidate_count = 11211`
- `no2cycle_failure_count = 7129`
- `does_no2cycle_hold = false`

This moves the active blocker again. Raw `minus -> plus` is largely balanced by
`plus -> minus`, and the BT proxy signed imbalance decays on this batch. The
current failing diagnostic is persistent cross-shell flip cycling under the v1
packet-ID no-2-cycle proxy.

The replay and receipt are diagnostic-only. They do not prove theorem-grade BT
distance, signed source summability, net-residue Lyapunov closure, physical
bridge, stretch absorption, no finite-time blowup, or Clay/Navier-Stokes
regularity.
