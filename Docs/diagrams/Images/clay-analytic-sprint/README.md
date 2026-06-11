# Clay Analytic Sprint Evidence Bundle

Date: `2026-06-02`
Status: empirical/diagnostic artifact bundle; non-promoting.

This directory contains the CSV and plot artifacts supplied for the Clay
analytic sprint documentation update. These files are evidence surfaces for
the current lemma roadmap. They do not prove PAWOTG density, Yang-Mills mass
gap, Navier-Stokes regularity, Gate 3 closure, or any Clay claim.

Verification summary: see `verification_summary.md`.

Checked synthesis receipt:
`DASHI/Physics/Closure/ClayComputedVisualizationSynthesisReceipt.agda`.
That receipt records the artifact readings as a fail-closed ledger and keeps
PAWOTG, Balaban transfer, NS danger-shell control, Gate 3 closure, YM mass gap,
NS regularity, and Clay promotion false.

Refined diagnostic receipt:
`DASHI/Physics/Closure/ClayRefinedDiagnosticTargetsReceipt.agda`.
That receipt records the second-pass calculations:
`Theta_global` versus `Theta_tail`, YM entropy-constant sensitivity, and Gate 3
sampler quality.  It is also fail-closed and non-promoting.

Monster re-2 quotient-control receipt:
`DASHI/Physics/Closure/MonsterMoonshineSSPQuotientControlReceipt.agda`.
That receipt records the Monster `q^2` / second-irrep stress model as an
effective-multiplicity-control target.  Raw Monster growth is not consumed as
YM polymer entropy, Gate 3 PAWOTG overlap entropy, or NS tail pressure unless a
carrier quotient theorem is supplied.

## Local Artifact Index

The following files were inspected in `Docs/Images/clay-analytic-sprint/`.
Matching source copies were also found under `/home/c/Downloads` for the CSVs
and for the same plot families.

| File | Kind | Columns or dimensions | SHA-256 prefix | Reading |
| --- | --- | --- | --- | --- |
| `computed_margin_summary.txt` | TXT | compact summary | `dc84138d6aa4ca42` | Uploaded human-readable summary of the refined NS/YM/Gate3 calculations. |
| `gate3_frame_extended.csv` | CSV | `sigma`, `N`, `dict_type`, `A_N`, `B_N`, `mu_N`, `N_minus_1_times_mu`, `gershgorin_lower`, `gershgorin_holds`, `frame_ratio`, `promotion_status` | `d4bccaf0189f0fa3` | Finite frame diagnostics for phase-blind and phase-complete toy dictionaries. |
| `gate3_sampler_quality.csv` | CSV | `sigma`, `N`, `dict_type`, `mu_N`, `target_mu_strict_1_over_N_minus_1`, `mu_over_target`, `N_minus_1_times_mu`, `gershgorin_lower`, `A_N`, `condition_number_proxy`, `sampler_quality`, `promotion_status` | generated | Refined sampler-quality diagnostic; every sampled row is clustered/failing. |
| `gate3_frame_sampler_quality.csv` | CSV | `sigma`, `N`, `dict_type`, `A_N`, `B_N`, `mu_N`, `N_minus_1_times_mu`, `gershgorin_lower`, `gershgorin_holds`, `frame_ratio`, `promotion_status`, `inv_N` | `ff1cf68854ffa822` | Uploaded sampler-quality summary with `inv_N`; same clustering conclusion. |
| `pawotg_sigma_crit.png` | PNG | `2400 x 1600`, RGBA | `1503926af8a303fe` | PAWOTG critical-spread plot. Numeric source data for `p=3, sigma_crit = 0.5052` was not present in the CSVs inspected here. |
| `pawotg_sigma_crit_1.png` | PNG | `2400 x 1600`, RGBA | `012ecbe8c56a766f` | Alternate PAWOTG critical-spread plot. |
| `pawotg_sigma_crit_2.png` | PNG | `2400 x 1600`, RGBA | `1503926af8a303fe` | Duplicate content of `pawotg_sigma_crit.png`. |
| `ym_p7_polymer_kp.csv` | CSV | `beta`, `c_min`, `p`, `a`, `r`, `KP_d1`, `KP_d2`, `KP_d3`, `KP_inf`, `converges`, `sum_lt_1`, `promotion_status` | `7932bcdee24b0eec` | `p=7` KP geometric-series diagnostics across beta values. |
| `ym_c0_threshold_sensitivity.csv` | CSV | `C0`, `r_target`, `kp_sum_at_target`, `beta_required`, `gap_from_beta6`, `p`, `a`, `c_min`, `promotion_status` | generated | Refined entropy-constant sensitivity table; `C0 > 1` raises the bridge threshold. |
| `ym_beta_threshold_sensitivity_C0.csv` | CSV | `C0`, `beta_convergence_r_eq_1`, `beta_absorption_r_eq_0_5`, `beta_strong_r_eq_0_25`, `gap_from_beta6_to_absorption` | `a63e5bf7835fe634` | Uploaded compact `C0` sensitivity table including `C0 = 0.5` and `0.75`. |
| `ym_kp_sum_vs_beta.png` | PNG | `2400 x 1600`, RGBA | `46a6e2d32bdd1dbd` | KP sum versus beta plot. |
| `ym_kp_sum_vs_beta_1.png` | PNG | `2400 x 1600`, RGBA | `08e4803fb6b9208e` | Alternate KP sum versus beta plot. |
| `ym_kp_sum_vs_beta_2.png` | PNG | `2400 x 1600`, RGBA | `46a6e2d32bdd1dbd` | Duplicate content of `ym_kp_sum_vs_beta.png`. |
| `ns_theta_full_sweep.csv` | CSV | `trace`, `nu`, `K_kolmogorov`, `k`, `theta_k`, `E_tail_k`, `Diss_tail_k`, `Flux_tail_k`, `K_star`, `Theta`, `margin`, `K_star_le_K_nu`, `promotion_status` | `da8abcfc1e81bcf4` | Full theta-profile diagnostic. |
| `ns_theta_tail_restricted.csv` | CSV | `trace`, `nu`, `K_kolmogorov`, `K_diss`, `theta_global`, `danger_shell_global`, `global_margin`, `theta_tail`, `danger_shell_tail`, `tail_margin`, `tail_rows`, `low_shell_warning`, `tail_barrier_pass`, `promotion_status` | generated | Refined NS diagnostic separating low-shell global danger from dissipative-tail danger. |
| `ns_global_vs_tail_theta_summary.csv` | CSV | `trace`, `nu`, `K_kolmogorov`, `K_diss`, `theta_global`, `danger_shell_global`, `margin_global`, `max_k_available`, `theta_tail`, `danger_shell_tail`, `margin_tail`, `tail_has_data` | `32c61e9c91a03bf2` | Uploaded compact global-vs-tail theta summary. |
| `ns_theta_profile.png` | PNG | `2400 x 1600`, RGBA | `37e73fabc5836d09` | Theta-profile plot. |
| `ns_theta_profile_1.png` | PNG | `2400 x 1600`, RGBA | `d401adc97f366227` | Alternate theta-profile plot. |
| `ns_theta_profile_2.png` | PNG | `2400 x 1600`, RGBA | `37e73fabc5836d09` | Duplicate content of `ns_theta_profile.png`. |
| `monster_re2_recalculation_summary.txt` | TXT | compact summary | `0521897168473318` | Uploaded Monster `q^2` / second-irrep entropy stress summary. |
| `ym_monster_re2_C0_thresholds.csv` | CSV | `C0_model`, `C0`, `beta_convergence`, `beta_absorption`, `beta_strong_r_0_25`, `gap_beta6_to_absorption`, `r_at_beta6`, `KP_inf_at_beta6` | `de091cb444744669` | Monster re-2 stress table for YM effective entropy `C0`. |
| `gate3_monster_re2_sigma_crit.csv` | CSV | `C0_model`, `C0`, `prime`, `sigma_crit` | `be202202817e34d0` | Monster re-2 stress table for Gate 3 PAWOTG sigma thresholds across inert primes. |
| `ns_monster_re2_low_shell_vs_tail_summary.csv` | CSV | `trace`, `nu`, `K_kolmogorov`, `K_diss`, `theta_global`, `danger_shell_global`, `margin_global`, `max_k_available`, `theta_tail`, `danger_shell_tail`, `margin_tail`, `tail_has_data`, `global_to_tail_ratio` | `396bb796ed1a01fc` | Monster re-2 NS low-shell-vs-tail stress summary. |
| `ym_monster_re2_beta_thresholds.png` | PNG | plot | `223a6ecd24d763e3` | YM beta thresholds under Monster re-2 entropy stress models. |
| `gate3_monster_re2_sigma_crit_p3.png` | PNG | plot | `a5713dbc12d1992a` | Binding `p=3` Gate 3 sigma threshold under Monster re-2 stress models. |
| `gate3_monster_re2_sigma_crit_all_inert.png` | PNG | plot | `5c64f7439426e6b4` | All-inert-prime Gate 3 sigma thresholds under Monster re-2 stress models. |
| `ns_monster_re2_global_tail_split.png` | PNG | plot | `dd4d14ee8545397e` | NS low-shell/global versus tail split under the Monster re-2 interpretation. |

Additional relevant `/home/c/Downloads` plot-only artifacts not currently
copied into this directory: `gate3_frame_lower_bound.png`,
`pawotg_overlap_series.png`, and `ym_kp_bridge_anatomy.png`.

## Computed Summary

- Gate 3: `gate3_frame_extended.csv` has 20 rows over `sigma in {0.45, 0.55}`,
  `N in {8, 16, 32, 64, 128}`, and `dict_type in {phase_complete,
  phase_blind}`. All 20 rows have `gershgorin_holds = False`; `A_N` reaches
  numerical zero, `B_N` reaches `27.34199769`, and the maximum `frame_ratio`
  is `2.73419976900602e+16`. This verifies the obstruction-style reading for
  this finite toy dictionary sweep only.
- PAWOTG: the directory contains PAWOTG critical-spread plots, but no
  machine-readable PAWOTG CSV with columns for `p` and `sigma_crit`. The claim
  `p=3, sigma_crit = 0.5052` cannot be numerically verified from the CSVs
  available in this bundle.
- YM: `ym_p7_polymer_kp.csv` verifies `r(beta=6) = 2.7017782` with `c_min =
  0.242`, `p = 7`, and `a = 0.5`. Recovering the exponential model
  `r(beta) = 11.541048919816665 * exp(-0.242 * beta)` from the rows gives the
  convergence threshold `r = 1` at `beta = 10.10706674055453` and the strict
  absorption threshold `r = 0.5` at `beta = 12.971311288322898`. The table's
  sampled row `beta = 12.97` has `r = 0.50015869` and `sum_lt_1 = False`;
  `beta = 13.64` has `r = 0.42529601`, `KP_inf = 0.74002621`, and
  `sum_lt_1 = True`.
- NS: `ns_theta_full_sweep.csv` has 320 rows across traces `kolmogorov`,
  `smooth`, `near_critical`, `inviscid`, and `rough`; viscosities `0.01` and
  `0.001`; and `k = 1..64`. Every row has `K_star = 2`,
  `K_star_le_K_nu = True`, and `promotion_status = NO_PROMOTION`. `Theta`
  ranges from `2.060518` to `15.640463`, and `margin` ranges from
  `-14.640463` to `-1.060518`, so the sweep verifies a diagnostic/failure
  regime, not a successful theta/HH closure.
- Refined NS: `ns_theta_tail_restricted.csv` shows that `theta_global` is
  dominated by the low shell `k = 2` for the sampled traces.  Restricting to
  the dissipative tail `k >= ceil(K_kolmogorov)` gives tail passes for
  `smooth` (`theta_tail = 0.00399397`) and `kolmogorov`
  (`theta_tail = 0.3188379`), while `near_critical` (`2.01585515`) and
  `rough` (`2.76304232`) still fail.  The `inviscid` row has no sampled
  tail row because `K_diss = 178` exceeds the `k <= 64` CSV range.
- Refined YM: `ym_c0_threshold_sensitivity.csv` and the uploaded compact
  `ym_beta_threshold_sensitivity_C0.csv` record
  `beta_abs(C0) = (a + log(2 p C0)) / c_min`.  With `C0 = 1`,
  strict absorption is `beta = 12.97131128`; with `C0 = 1.25`, it rises to
  `beta = 13.89339207`.  The uploaded table also shows `C0 = 0.5` gives
  `beta_abs = 10.10706673` and `C0 = 0.75` gives `11.78254238`.
  The entropy constant is therefore load-bearing.
- Refined Gate 3: `gate3_sampler_quality.csv` records zero Gershgorin-passing
  rows.  The current sampler has `mu_N` near `1`, while the strict row-sum
  target is `mu_N < 1/(N-1)`; every sampled row is marked `FAIL_CLUSTERED`.
- Monster re-2 stress model: `ym_monster_re2_C0_thresholds.csv` and
  `gate3_monster_re2_sigma_crit.csv` show why raw moonshine multiplicity must
  be quotiented before it enters physical entropy constants.  Baseline
  `C0_eff = 1` keeps YM strict absorption at `beta_abs = 12.971311`; a
  square-root Monster leak raises it to about `22.66`, and raw `c2/c1` leakage
  raises it to about `32.36`.  For Gate 3 at binding `p=3`, baseline
  `sigma_crit = 0.505208`; square-root leakage tightens this to about `0.296`,
  and raw leakage tightens it to about `0.228`.  The new shared blocker is
  effective multiplicity control, not a new closure theorem.

Promotion status for every artifact in this directory is `NO_PROMOTION`.
