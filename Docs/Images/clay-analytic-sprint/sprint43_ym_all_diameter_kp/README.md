# Sprint 43 YM All-Diameter KP Artifact Contract

Status: diagnostic artifact directory; non-promoting.

The Sprint 43 harness writes:

```text
ym_all_diameter_kp_rho_leakage_table.csv
ym_all_diameter_kp_rho_leakage_checks.json
ym_all_diameter_kp_rho_leakage_manifest.json
```

Every artifact must carry:

```text
promotion_status = NO_PROMOTION_DIAGNOSTIC_ONLY
```

or the aggregate JSON status:

```text
NO_PROMOTION_FAIL_CLOSED
```

The table records per-row beta, p, c_min, a, C0, effective leakage multiplier,
geometric ratio, all-diameter KP sum, leakage tail, rho target pass, strict
margin, connected-animal side diagnostic, proof certificates, and fail-closed
reason.

Numeric rows are evidence only.  A row is not proof-gate passing unless the
five certificate columns are explicitly true:

```text
actual_activity_certified
all_diameter_certified
uniform_constants_certified
overlap_compatibility_certified
tail_closure_certified
```

No artifact in this directory proves continuum Yang-Mills, Balaban transfer,
OS/Wightman reconstruction, a mass gap, or Clay Yang-Mills.
