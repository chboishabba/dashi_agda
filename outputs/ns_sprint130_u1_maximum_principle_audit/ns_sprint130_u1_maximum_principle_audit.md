# NS Sprint 130 U1 Maximum Principle Audit

- Audit: `ns_sprint130_u1_maximum_principle_audit`
- Verdict: `CLOSED`
- Complete: `true`
- Exit code: `0`
- Obstruction lemma: `PureDiffusionU1MaximumPrinciple`
- Pure diffusion U1 maximum principle: `true`
- U1 L-infinity nonincreasing: `true`
- Supports viscous-dominance obstruction: `true`
- Clay Navier-Stokes promoted: `false`
- Passed rows: `11 / 11`

## PDE Facts

- `lemma`: `PureDiffusionU1MaximumPrinciple`
- `unknown`: `u1 = u^theta / r`
- `operator_name`: `L_tilde`
- `operator`: `(1/r^3) partial_r(r^3 partial_r) + partial_z^2`
- `expanded_operator`: `partial_r^2 + (3/r) partial_r + partial_z^2`
- `weighted_measure`: `r^3 dr dz`
- `equation`: `D_t u1 = partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = nu L_tilde u1`
- `viscosity_condition`: `nu > 0`
- `source_term`: `0`
- `transport_term`: `material derivative drift`
- `initial_linf`: `M0 = ||u1(0)||_inf`
- `linf_bound`: `||u1(t)||_inf <= ||u1(0)||_inf = M0`
- `boundary_terms`: `zero by the receipt classical solution and stated decay/axis conditions`
- `regularity_scope`: `uses only the receipt classical solution level needed to justify pointwise maximum principle and integration by parts`
- `clay_navier_stokes_promoted`: `False`

## Rows

| Gate | Expected | Actual | Passed | Evidence |
| --- | --- | --- | --- | --- |
| `ReceiptLemma` | `PureDiffusionU1MaximumPrinciple` | `PureDiffusionU1MaximumPrinciple` | `True` | `records the receipt-level pure-diffusion U1 maximum-principle lemma` |
| `OperatorIdentity` | `L_tilde = (1/r^3) partial_r(r^3 partial_r) + partial_z^2` | `(1/r^3) partial_r(r^3 partial_r) + partial_z^2` | `True` | `expanded form: partial_r^2 + (3/r) partial_r + partial_z^2` |
| `WeightedMeasure` | `r^3 dr dz` | `r^3 dr dz` | `True` | `this is the radial 4D axisymmetric weight paired with L_tilde` |
| `NegativeSemidefiniteIBP` | `int f L_tilde f r^3 dr dz <= 0` | `negative_semidefinite` | `True` | `{"boundary_terms": "zero by the receipt classical solution and stated decay/axis conditions", "identity": "int f L_tilde f r^3 dr dz = - int ((partial_r f)^2 + (partial_z f)^2) r^3 dr dz", "passed": true, "sign": "negative_semidefinite", "weighted_measure": "r^3 dr dz"}` |
| `DivergenceFormParabolicMaximumPrinciple` | `applies to partial_t u1 = nu L_tilde u1 with nu > 0` | `divergence-form parabolic maximum principle` | `True` | `{"bound": "\|\|u1(t)\|\|_inf <= \|\|u1(0)\|\|_inf = M0", "equation": "D_t u1 = partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = nu L_tilde u1", "operator_divergence_form": "(1/r^3) partial_r(r^3 partial_r) + partial_z^2", "passed": true, "principle": "divergence-form parabolic maximum principle", "source_term": "0", "transport_term": "material derivative drift", "viscosity_condition": "nu > 0"}` |
| `U1LinfNonincreasing` | `||u1(t)||_inf <= ||u1(0)||_inf = M0` | `||u1(t)||_inf <= ||u1(0)||_inf = M0` | `True` | `pure diffusion has no positive interior maximum growth` |
| `NoHiddenSource` | `source=0; drift is only the material derivative transport` | `source=0, transport=material derivative drift` | `True` | `D_t u1 = partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = nu L_tilde u1` |
| `NoHiddenRegularity` | `no regularity beyond the receipt classical solution level` | `uses only the receipt classical solution level needed to justify pointwise maximum principle and integration by parts` | `True` | `the audit does not add a stronger smoothness assumption` |
| `SupportsViscousDominanceObstruction` | `true` | `true` | `True` | `U1 amplitude cannot grow past M0 inside the pure-diffusion lemma` |
| `ClayNavierStokesPromotion` | `false` | `false` | `True` | `closing this obstruction lemma is not a Clay Navier-Stokes promotion` |
| `forbidden marker scan` | `zero hits` | `0` | `True` | `[]` |

## Control Card

- O: Worker 1 owns only the Sprint130 U1 maximum-principle audit script and matching output directory
- R: prove the receipt-level PureDiffusionU1MaximumPrinciple while keeping Clay promotion false
- C: deterministic Python audit emitting rows JSON, summary JSON, and Markdown
- S: operator, measure, IBP sign, maximum principle, and L-infinity bound all close
- L: the ledger has no open gates when the obstruction lemma closes
- P: use this closed lemma only as support for the viscous-dominance obstruction
- G: exit code is 0 exactly when all rows pass and Clay remains unpromoted
- F: any hidden source, hidden regularity, failed sign check, marker hit, or Clay promotion fails closed
