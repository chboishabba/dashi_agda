# Clay Sprint 43 NS Residue Semantics Audit

Date: 2026-06-04

This records the fail-closed side-by-side audit of candidate `R_plus_K`
definitions on the repaired 3D Navier-Stokes truth artifacts.  The Sprint 44
audit supersedes the earlier Sprint 43 exploratory names with the candidate
surfaces requested for the falsification frontier.

The audit is emitted by `scripts/ns_diagnostic_harness.py` as:

- `ns_residue_semantics_audit.csv`
- `ns_residue_semantics_wide.csv`
- `ns_residue_theta_grid_summary.csv`
- `residue_semantics_summary` in `ns_diagnostic_checks.json`

## Semantics Compared

- `Rplus_strict`: current coherent, non-Beltrami, not-pressure-decorrelated
  classifier.
- `Rplus_strain`: principal positive-strain alignment residue.
- `Rplus_stretchSign`: direct positive signed stretching share.
- `Rplus_pressureRelaxed`: strict coherence/non-Beltrami gates, with pressure
  downgrade only above the high threshold.
- `Rplus_noPressure`: non-Beltrami positive-strain residue with no pressure
  downgrade.

## Artifact Roots

- `Docs/Images/clay-analytic-sprint/sprint43_ns3d_seed0_residue_audit/`
- `Docs/Images/clay-analytic-sprint/sprint44_residue_semantics_N64_seed0/`
- `Docs/Images/clay-analytic-sprint/sprint44_residue_semantics_N64_seed1/`

## Results

| run | best finite-ratio semantic at theta=1 | ratio rows | sup adjusted ratio | inf budget | result |
| --- | --- | ---: | ---: | ---: | --- |
| N64 seed0 | `Rplus_stretchSign` | 702 / 728 | `0.071772764128325409` | `-0.00099515119744580786` | ratio gap + budget fail |
| N64 seed1 | `Rplus_stretchSign` | 702 / 728 | `0.0056805288947764212` | `-0.0017769118671767253` | ratio gap + budget fail |

At theta `1.0`, `Rplus_strict` and `Rplus_pressureRelaxed` both fail on
`208 / 728` rows with `zeroR_positiveQ`, meaning `Q_K > 0` while `R_plus_K`
is zero.  `Rplus_strain`, `Rplus_noPressure`, and `Rplus_stretchSign` make the
adjusted bridge ratio finite on `702 / 728` rows for both N64 seeds, but still
leave ratio gaps.  The best observed theta `1.0` ratio is `Rplus_stretchSign`.

Theta-grid sensitivity:

| run | semantic | theta 0 sup C | theta 0.25 sup C | theta 0.5 sup C | theta 1 sup C |
| --- | --- | ---: | ---: | ---: | ---: |
| N64 seed0 | `Rplus_stretchSign` | `0.45962021722920082` | `0.2889277534846087` | `0.18162657690933098` | `0.071772764128325409` |
| N64 seed1 | `Rplus_stretchSign` | `0.030748156399259732` | `0.020158652776115189` | `0.013216118601431338` | `0.0056805288947764212` |

The concentration penalty is not the immediate culprit in these two N64 runs:
larger theta reduces the adjusted ratio, but the source budget remains below
the required threshold:

```text
budget_K = gamma_K + eta_K log_2(p) - theta beta_K
```

At theta `0`, the budget infimum is `0`, still not `> 1/2`.  At theta `1`, it
is approximately `-0.000995` on N64 seed0 and `-0.001777` on N64 seed1.

## Boundary

This audit localizes the next blocker.  The route is not rescued by changing
theta or by pressure relaxation.  It is blocked by:

- zero `Rplus` with positive `Q` for strict and pressure-relaxed definitions;
- ratio gaps for strain/no-pressure/stretch-sign definitions;
- lack of proof authority for stretch-sign and strain diagnostics;
- missing actual ternary lineage estimates;
- `budget_K <= 1/2` even when relaxed semantics make ratios finite;
- missing stretch-absorption and no-blowup implications.

No NS, Gate3, YM, terminal theorem, or Clay promotion flag changes.
