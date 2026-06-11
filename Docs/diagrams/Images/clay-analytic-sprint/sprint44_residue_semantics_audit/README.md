# Sprint 44 Residue Semantics Audit Artifacts

This directory is reserved for Sprint 44 NS 3D residue-semantics reruns.  Do
not overwrite Sprint 43 repaired evidence directories.

Expected run directories:

```text
N32_seed0/
N64_seed0/
N64_seed1/
```

Each run directory should contain:

```text
ns_diagnostic_table.csv
ns_bridge_budget_table.csv
ns_residue_semantics_audit.csv
ns_residue_semantics_wide.csv
ns_residue_theta_grid_summary.csv
ns_diagnostic_checks.json
ns_diagnostic_manifest.json
```

Canonical command shape:

```bash
python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz \
  --residue-semantics-audit \
  --theta-grid 0 0.25 0.5 1.0 \
  --progress-every 100 \
  --out-dir Docs/Images/clay-analytic-sprint/sprint44_residue_semantics_audit/N64_seed0
```

The artifacts are diagnostics only.  They do not promote NS, Gate3, YM, or
Clay status.
