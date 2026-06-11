# Clay Sprint 42 NS Diagnostic Harness

Sprint 42 implements the bridge-falsifier surface instead of adding another
proof sketch.

Executable harness:

```text
scripts/ns_diagnostic_harness.py
```

Outputs:

```text
ns_diagnostic_table.csv
ns_bridge_budget_table.csv
ns_diagnostic_checks.json
ns_diagnostic_manifest.json
```

The table records, per `(K,t)`:

```text
||omega_K||_2^2, D_K, T_K, Q_K
Rminus_K, Rzero_K, Rplus_K, netResidue_K
BeltramiDefect_K, DirectionCoherenceDefect_K
PressureDecorrelationScore_K, AlignedConcentration_K
M_(+,-), M_(+,0), M_(+,+), s_K, s_eff_K, 2^(K/2)*s_eff_K
C_K, gamma_K, eta_K, p, beta_K, theta, budget_K, rho_K
```

The bridge-budget table additionally records the Sprint 40/42 estimator
surface:

```text
step, time, K, shell_enstrophy, tail_enstrophy, D_K, theta_NS_K
Q_K_proxy, R_plus_K_proxy, aligned_concentration_K
beta_hat_K, gamma_hat_K, eta_hat_K, budget_hat_K
adjusted_bridge_ratio, promotion_status
```

Pass criteria recorded by the harness:

```text
sup C_K finite
sup M_(+,+) < 1/sqrt2
finite observed weighted source prefix
inf budget_K > 1/2
```

Fail types:

```text
FAIL TYPE 1: C_K unbounded
FAIL TYPE 2: M_(+,+) >= 1/sqrt2
FAIL TYPE 3: weighted source diverges
FAIL TYPE 4: budget_K <= 1/2
```

Governance boundary:

Current sibling `../dashiCFD` truth artifacts are 2D scalar vorticity traces.
For those traces the harness records a fail-closed branch:

```text
diagnostic_mode = 2d_scalar_fail_closed_no_3d_stretching
physical_bridge_available = false
clay_navier_stokes_promoted = false
```

The 3D vector branch computes direct spectral diagnostics on periodic smoke or
future 3D vector-vorticity truth data, but the transition/source lineage row is
still an observed shell-ratio diagnostic, not an analytic theorem.

Validation:

```text
python scripts/ns_diagnostic_harness.py --smoke --smoke-n 8 --smoke-samples 2 --out-dir /tmp/ns_diagnostic_harness_smoke3d
python scripts/ns_diagnostic_harness.py --ev5-dir ../dashiCFD/outputs/ns_ev5_worker5_N32_seed0_tail2 --out-dir /tmp/ns_diagnostic_harness_ev5
python scripts/ns_diagnostic_harness.py --truth /tmp/ns_diag_2d_truth.npz --out-dir /tmp/ns_diagnostic_harness_2d
agda -i . -i cubical -i DCHoTT-Agda DASHI/Physics/Closure/ClaySprintFortyTwoNSDiagnosticHarnessReceipt.agda
```

All validation remains diagnostic-only. No NS regularity theorem, no stretch
absorption theorem, no no-blowup theorem, and no Clay promotion are claimed.
