# Clay Sprint 44 Residue Semantics Audit

Date: 2026-06-04

Sprint 44 turns the repaired 3D Navier-Stokes truth lane into a sharper
bridge falsifier.  The question is no longer whether the harness can compute
`Q_K`; it can.  The question is which, if any, proof-defensible `Rplus_K`
semantics controls that physical stretching after concentration correction.

The executable surface is:

```bash
python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz \
  --residue-semantics-audit \
  --theta-grid 0 0.25 0.5 1.0 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint44_residue_semantics_audit/N64_seed0
```

## Output Contract

Each run still writes the Sprint 42/43 tables:

```text
ns_diagnostic_table.csv
ns_bridge_budget_table.csv
ns_diagnostic_checks.json
ns_diagnostic_manifest.json
```

Sprint 44 adds:

```text
ns_residue_semantics_audit.csv
ns_residue_semantics_wide.csv
ns_residue_theta_grid_summary.csv
```

The audit table emits one row per `(K,time,semantic,theta)` and records
`Q_K`, concentration, semantic `Rplus_K`, adjusted bridge ratio,
`zeroR_positiveQ`, `beta/gamma/eta`, budget, and fail-closed promotion status.
The wide table pivots the same audit by `(K,time,theta)` for quick comparison.

## Audited Semantics

```text
Rplus_strict
Rplus_strain
Rplus_stretchSign
Rplus_pressureRelaxed
Rplus_noPressure
```

`Rplus_strict` is the current DASHI red classifier.  `Rplus_strain` is a
principal positive-strain alignment residue and is intentionally separate from
`Rplus_stretchSign`, the direct positive stretching sign share.

`Rplus_pressureRelaxed` tests whether pressure decorrelation downgrades red too
aggressively.  `Rplus_noPressure` removes pressure downgrade entirely while
keeping the non-Beltrami strain-alignment requirement.

## Interpretation

The useful failures are named:

```text
FAIL_ZERO_RPLUS_POSITIVE_Q
FAIL_RATIO_UNAVAILABLE
FAIL_BUDGET_BELOW_HALF
```

If every semantic has `zeroR_positiveQ` rows or unavailable bridge ratios, the
residue route is structurally failing under the tested definitions.  If only
relaxed pressure/no-pressure variants survive, pressure remains diagnostic and
cannot downgrade red until a proof justifies it.  If only stretch-sign survives,
the route has a physical sign proxy but not a geometric DASHI residue.

## Recorded Runs

Artifact root:

```text
Docs/Images/clay-analytic-sprint/sprint44_residue_semantics_audit/
```

Theta `1.0` summary:

| run | semantic | ratio rows | zeroR positiveQ | sup adjusted ratio | inf budget | interpretation |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| N32 seed0 | Rplus_strict | 1 | 293 | `1.31e-45` | `-0.02572` | `FAIL_ZERO_RPLUS_POSITIVE_Q` |
| N32 seed0 | Rplus_stretchSign | 567 | 0 | `0.11224` | `-0.02572` | `FAIL_RATIO_UNAVAILABLE` |
| N64 seed0 | Rplus_strict | 0 | 208 | unavailable | `-0.000995` | `FAIL_ZERO_RPLUS_POSITIVE_Q` |
| N64 seed0 | Rplus_stretchSign | 702 | 0 | `0.07177` | `-0.000995` | `FAIL_RATIO_UNAVAILABLE` |
| N64 seed1 | Rplus_strict | 0 | 208 | unavailable | `-0.001777` | `FAIL_ZERO_RPLUS_POSITIVE_Q` |
| N64 seed1 | Rplus_stretchSign | 702 | 0 | `0.005681` | `-0.001777` | `FAIL_RATIO_UNAVAILABLE` |

The strict red classifier misses positive physical stretching on observed
rows.  The stretch-sign and strain variants make the bridge numerically sane
on most rows, but they are diagnostic relaxations and still do not close the
budget or ratio-availability gates.

## Boundary

This is a falsification harness only.  It does not prove the physical bridge,
actual ternary lineage, stretch absorption, no finite-time blowup, or Clay
Navier-Stokes regularity.  All promotion flags remain false.
