# Clay Sprint 40 Bridge-Budget Estimator Run

Date: 2026-06-03

This records the Sprint 40 upgrade of `scripts/ns_diagnostic_harness.py` into a
bridge-observable generator surface.  The script now emits:

- `ns_diagnostic_table.csv`
- `ns_bridge_budget_table.csv`
- `ns_diagnostic_checks.json`
- `ns_diagnostic_manifest.json`

The bridge-budget table uses the requested field contract:

```text
step,time,K,
shell_enstrophy,
tail_enstrophy,
D_K,
theta_NS_K,
Q_K_proxy,
R_plus_K_proxy,
aligned_concentration_K,
beta_hat_K,
gamma_hat_K,
eta_hat_K,
budget_hat_K,
adjusted_bridge_ratio,
promotion_status
```

Extra columns record `field_status`, `unavailable_reason`, and
`diagnostic_mode` so proxy and blocked fields cannot be mistaken for proof
inputs.

## Runs

Output root:

- `Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/`

Commands:

```bash
python scripts/ns_diagnostic_harness.py \
  --ev5-dir ../dashiCFD/outputs/ns_ev5_worker5_N32_seed0_tail2 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/ns_ev5_worker5_N32_seed0_tail2

python scripts/ns_diagnostic_harness.py \
  --ev5-dir ../dashiCFD/outputs/ns_ev5_worker5_N32_seed1_tail2 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/ns_ev5_worker5_N32_seed1_tail2

python scripts/ns_diagnostic_harness.py \
  --smoke --smoke-n 16 --smoke-samples 3 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/synthetic_3d_smoke
```

Validation:

```bash
python -m py_compile scripts/ns_diagnostic_harness.py
```

## Results

| run | mode | K_star | nonzero shells at/above K_star | high-shell support | physical bridge | inf budget | verdict |
| --- | --- | ---: | --- | --- | --- | ---: | --- |
| `ns_ev5_worker5_N32_seed0_tail2` | `2d_scalar_fail_closed_no_3d_stretching` | 2 | `[2,3,4]` | fail | unavailable | 0.0 | `NO_PROMOTION_BLOCKED_NO_3D_STRETCHING` |
| `ns_ev5_worker5_N32_seed1_tail2` | `2d_scalar_fail_closed_no_3d_stretching` | 2 | `[2,3,4]` | fail | unavailable | 0.0 | `NO_PROMOTION_BLOCKED_NO_3D_STRETCHING` |
| `synthetic_3d_smoke` | `3d_vector_direct_spectral` | 0 | `[0]` | fail | diagnostic only | `3.79801067982192e-15` | `NO_PROMOTION_HIGH_SHELL_SUPPORT_FAIL` |

The two real `../dashiCFD` tail-resolved traces are useful because they resolve
`K_star = 2`, unlike the earlier `K_star = 9` CPU trace.  They still fail the
Sprint 40 bridge-budget gate for two independent reasons:

- the truth artifacts are 2D scalar vorticity, so literal 3D
  `omega dot grad(u) omega` stretching and physical `Q_K` are unavailable;
- only three nonzero shells, `[2,3,4]`, are present at or above `K_star`, below
  the five-shell minimum fit gate.

The synthetic 3D smoke run confirms the direct 3D vector-vorticity code path is
executable, but it is not a physical NS trace and its budget remains far below
the required `> 1/2` threshold.

## SPV/SIMD Boundary

Readable sibling artifacts show useful Vulkan/vkFFT/SPV infrastructure:

- `../dashiCFD/vulkan_les_backend.py`
- `../dashiCFD/vulkan_encode_backend.py`
- `../dashiCFD/vulkan_decode_backend.py`
- `../dashiCFD/dashiCORE/spv/`
- `../dashiCORE/spv/`

These are direct-use acceleration surfaces for 2D LES observable generation.
They do not currently provide a 3D Navier-Stokes solver or a formal proof that
concrete SPV kernels implement the bridge-observable semantics.  The strongest
formal local precedent is `SWAR_Equivalence.agda`, which gives an abstract
packed-lane refinement pattern, not shader verification.

## Bottom Line

The repo now has the requested reproducible Sprint 40 bridge-budget CSV
surface.  Current data remains fail-closed: the real traces are 2D and
under-supported at high shells, while the 3D branch is smoke-only.  No NS,
Gate3, YM, terminal, or Clay promotion flag changes.
