# Clay Sprint 43 YM All-Diameter KP/Rho/Leakage Harness

Sprint 43 is the Yang-Mills analogue of the NS diagnostic harness, but scoped
to the carrier-side p=7 KP/rho/leakage interface.

The question is not whether finite p=7 rows look good.  The question is:

```text
does the finite/local p=7 polymer evidence extend to an all-diameter,
volume/depth/scale-uniform KP activity envelope?
```

The executable harness is:

```text
scripts/ym_all_diameter_kp_rho_leakage_harness.py
```

It consumes either local CSV evidence or deterministic smoke rows, then emits:

```text
ym_all_diameter_kp_rho_leakage_table.csv
ym_all_diameter_kp_rho_leakage_checks.json
ym_all_diameter_kp_rho_leakage_manifest.json
```

## Live Formula

For each beta row, the geometric all-diameter diagnostic is:

```text
C0_eff = C0 * leakage_multiplier
r = p * C0_eff * exp(a - beta*c_min)
KP_prefix(D) = Sum_{d=1..D} r^d
KP_inf = r / (1-r)
tail_after_D = r^(D+1)/(1-r)
strict_log_margin = beta*c_min - a - log(2*p*C0_eff)
```

The strict numeric carrier-KP diagnostic passes only when:

```text
r < 1
KP_inf < 1
strict_log_margin > 0
rho_geom <= rho_target
```

The harness also computes the connected-animal side diagnostic separately:

```text
ca_q = C0_eff * exp(a - beta*c_min)
ca_pq = p * ca_q
ca_sum = ca_q / (1 - p*ca_q)^2
```

These two surfaces are deliberately kept separate.

## Proof Gate

Numeric KP success does not promote Yang-Mills.  The proof gate requires all
of these certificate columns to be present and true:

```text
actual_activity_certified
all_diameter_certified
uniform_constants_certified
overlap_compatibility_certified
tail_closure_certified
```

If those certificates are absent, the harness records the row as fail-closed
even when the numeric tail is small.

## Pass/Fail Meanings

PASS, diagnostic only:

```text
some row passes numeric KP/rho/leakage checks
and all proof certificate columns are true
```

FAIL TYPE 1:

```text
r >= 1 or KP_inf diverges
```

Meaning: the all-diameter tail is not summable at that beta/C0 row.

FAIL TYPE 2:

```text
KP_inf >= 1 or strict_log_margin <= 0
```

Meaning: convergence is not strong enough for strict KP absorption.

FAIL TYPE 3:

```text
certificates missing
```

Meaning: the row is finite/local or symbolic, not an all-diameter Wilson
activity theorem.

FAIL TYPE 4:

```text
leakage tail non-finite or nonuniform C0/leakage multiplier
```

Meaning: leakage or entropy stress defeats the usable margin.

## Boundary

This harness can at most localize the carrier KP/activity gate.  It does not
prove:

```text
ContinuumUniformRhoBound
ContinuumUniformLeakageBound
YMBalabanContinuumLimitWithUsableMargin
OS/Wightman reconstruction
Yang-Mills mass gap
Clay Yang-Mills
```

All promotion fields remain false.
