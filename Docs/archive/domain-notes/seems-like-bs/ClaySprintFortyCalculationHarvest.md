# Clay Sprint 40 Calculation Harvest

Date: 2026-06-03

This harvest answers what can be calculated locally from this repo and nearby
`../dashi*` workspaces for the current Clay Sprint 40 blockers.  The generated
artifacts are under:

- `Docs/Images/clay-analytic-sprint/sprint40_calc/`
- `Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/`

All rows are diagnostic or evidence-only.  No NS, YM, Gate3, terminal, or Clay
promotion is justified by these calculations.

## Sources run

- `../dashiCFD/scripts/ns_theta_full_sweep.py`
  - output: `sprint40_calc/ns_theta_full_sweep.csv`
  - computes synthetic shell-tail `theta(k,t)` profiles over five regimes and
    five viscosities.
- `../dashiCFD/scripts/ns_ev5_shell_enstrophy.py`
  - output: `sprint40_calc/ns_ev5_cpu/`
  - consumes `../dashiCFD/outputs/truth_ns_ev5_cpu_2026-06-01T014101.npz`
    and computes shell enstrophy, EV5 trace, and checks.
- `scripts/ns_diagnostic_harness.py`
  - output: `sprint40_bridge_budget/`
  - consumes the tail-resolved sibling EV5 directories
    `../dashiCFD/outputs/ns_ev5_worker5_N32_seed0_tail2` and
    `../dashiCFD/outputs/ns_ev5_worker5_N32_seed1_tail2`, resolving their
    source truth NPZ files through each manifest, and emits the Sprint 40
    bridge-budget CSV contract.
- `../dashiCFD/scripts/gate3_frame_extended_sweep.py`
  - output: `sprint40_calc/gate3_frame_extended.csv`
  - computes finite atom-frame diagnostics for `N = 8, 16, 32, 64`.
- `../dashiCFD/scripts/ym_p7_polymer_enumerator.py`
  - output: `sprint40_calc/ym_p7/ym_p7_polymer_enumerator.csv`
  - enumerates the local p=7 diameter 1 and 2 polymer diagnostic.
- `../dashiCFD/scripts/ym_p7_polymer_enumerator_d3.py`
  - output: `sprint40_calc/ym_p7_d3.csv`
  - computes the p=7 diameter 1 through 3 activity-bound table.

## Results

### NS theta sweep

The sweep produced 1600 rows.  The observed global danger shell is always
`k = 1`, so the main observed hazard remains low-shell rather than a proven
high-shell decay theorem.  Tail values sit at or just above the boundary:

- rough trace global maxima range from `1.0408363316717624` to
  `1.1028037662310666`, all at `k = 1`.
- inviscid trace global maxima range from `1.029003777196406` to
  `1.0510226018402122`, all at `k = 1`.
- kolmogorov trace global maxima range from `1.0001249718247474` to
  `1.013046459604463`, all at `k = 1`.
- near-critical and smooth traces sit at `1.0`.

This can support W1/W5 falsification or boundary-localization work, but it
does not provide the Sprint 40 bridge
`Q_K <= C R_K^+ concentration_K^theta`, actual `beta`, actual `gamma`, actual
`eta`, or a strict high-shell budget.

### NS EV5 truth trace

The EV5 adapter reports:

- `K_star = 9`
- `v7_decreasing = true`
- `v2_bounded = true`
- `ev5_admissible = true`
- normalization guard passed
- `q_increases = 1`
- `two_phase_ok = false`
- `evaluation_status = falsified`
- theta profile unavailable because the finite vector has no shell cutoffs at
  or above `K_star`.

This is useful as a reproducible diagnostic failure surface for the current
encoding.  It is not a Navier-Stokes theorem and does not close W1 or W5.

### NS bridge-budget estimator

The upgraded local harness now writes `ns_bridge_budget_table.csv` with the
requested columns:

```text
step,time,K,shell_enstrophy,tail_enstrophy,D_K,theta_NS_K,
Q_K_proxy,R_plus_K_proxy,aligned_concentration_K,beta_hat_K,
gamma_hat_K,eta_hat_K,budget_hat_K,adjusted_bridge_ratio,
promotion_status
```

The two real tail-resolved dashiCFD runs give:

- `ns_ev5_worker5_N32_seed0_tail2`: `K_star = 2`, nonzero shells at or above
  `K_star` are `[2,3,4]`, `high_shell_support_pass = false`,
  `physical_bridge_available = false`, `inf_budget_K = 0.0`.
- `ns_ev5_worker5_N32_seed1_tail2`: `K_star = 2`, nonzero shells at or above
  `K_star` are `[2,3,4]`, `high_shell_support_pass = false`,
  `physical_bridge_available = false`, `inf_budget_K = 0.0`.

Both real traces are `2d_scalar_fail_closed_no_3d_stretching`: literal 3D
`omega dot grad(u) omega`, physical `Q_K`, physical `R_K^+`, and adjusted
bridge ratios are unavailable.  They also fail the five-nonzero-high-shell fit
gate.  A synthetic 3D smoke run confirms the direct 3D vector code path
executes, but it is not a physical trace and still fails the high-shell/budget
gates.

### Gate3 atom-frame sweep

The Gate3 finite frame calculation remains clustered:

- phase-complete `A_N` ranges down to `9.7168302646e-08`.
- phase-complete frame ratio reaches `431911263.896`.
- phase-blind frame ratio stabilizes near `353`.
- `max_crossterm = 1` for the sampled dictionaries.
- best reported net quality is only `0.00175076744074`.

This is useful for sampler-quality and PAWOTG counterexample search.  It does
not prove uniform separation, Mosco convergence, no-pollution, or mass-shell
transfer.

### YM p=7 polymer diagnostics

The local diameter 1 and 2 enumerator stays non-promoting and has large
finite ratios:

- diameter 1 count is `15`; weighted sums are about `40.77`.
- diameter 2 count is `176`; weighted sums are about `788.78`.

The diameter 1 through 3 bound table shows the cumulative ratio crosses the
normalised threshold for lower beta and becomes small only at high diagnostic
beta:

- beta `6`: cumulative ratio through diameter 3 is `29.7232985113`.
- beta `7.69`: cumulative ratio through diameter 3 is `10.7986440908`.
- beta `10.13`: cumulative ratio through diameter 3 is `2.96691547847`.
- beta `13.64`: cumulative ratio through diameter 3 is `0.683098850852`.
- beta `16.7`: cumulative ratio through diameter 3 is `0.252282568378`.

This can support YM activity-bound exploration.  It does not close actual
all-diameter KP, Balaban physical beta transfer, OS positivity, Wightman
reconstruction, or the mass-gap theorem.

## Highest-alpha next calculations

1. Generate or import a real 3D incompressible NS velocity/vorticity trace
   with enough nonzero high-shell support: at least five nonzero shells at or
   above declared `K_star`.
2. Replace the current 2D fail-closed `Q_K_proxy/R_plus_K_proxy` columns with
   physical 3D stretching and residue observables.
3. Add concentration-profile regression to estimate candidate `beta_K` from
   shell mass alignment, with explicit confidence and failure criteria.
4. Replace Gate3 clustered dictionary sampling with a separation-controlled
   sampler and record whether `max_crossterm` decays with `N`.
5. Extend the YM p=7 activity diagnostic beyond diameter 3 using actual
   polymer classes or produce a rigorous entropy/action upper bound.  The
   current D1-D3 table is only a finite toy/local bound.

## Bottom line

Yes, there are useful calculations available locally, especially from
`../dashiCFD`.  They are most valuable as blocker localizers and falsification
surfaces.  The calculations run here do not solve Clay and do not discharge
the Sprint 40 P0 blockers.
