# NS Sprint 131 Source Upper Bound Audit

- Audit: `ns_sprint131_source_upper_bound_audit`
- Verdict: `CLOSED`
- Complete: `true`
- Exit code: `0`
- Lemma: `RigorousSourceUpperBound`
- Source upper bound closed: `true`
- Uses U1 maximum principle: `true`
- Quadratic source obstructed: `true`
- Clay Navier-Stokes promoted: `false`
- Passed rows: `11 / 11`

## Recorded Inputs

- `sprint130_receipt.source_path`: `/home/c/Documents/code/dashi_agda/outputs/ns_sprint130_u1_maximum_principle_audit/ns_sprint130_u1_maximum_principle_audit_summary.json`
- `sprint130_receipt.contract`: `ns_sprint130_u1_maximum_principle_audit`
- `sprint130_receipt.lemma`: `PureDiffusionU1MaximumPrinciple`
- `sprint130_receipt.complete`: `True`
- `sprint130_receipt.exit_code`: `0`
- `sprint130_receipt.clay_navier_stokes_promoted`: `False`
- `sprint130_receipt.u1_linf_nonincreasing`: `True`
- `sprint130_receipt.linf_bound`: `||u1(t)||_inf <= ||u1(0)||_inf = M0`
- `sprint130_receipt.accepted`: `True`

## Source Bound

- `lemma`: `RigorousSourceUpperBound`
- `u1_linf_input`: `||u1(t)||_inf <= ||u1(0)||_inf = M0`
- `concentration_scale`: `delta=tau^beta`
- `beta`: `9/20`
- `beta_float`: `0.45`
- `source_identity`: `partial_z(u1^2)=2 u1 partial_z u1`
- `derivative_scale`: `|partial_z u1| <= C_u M0/delta = C_u M0 tau^(-beta)`
- `derivative_scale_origin`: `receipt-level scaling upper bound`
- `chosen_constant`: `C_source=2*C_u`
- `chosen_bound`: `|partial_z(u1^2)| <= C_source M0^2 tau^(-beta)`
- `chosen_bound_exponent`: `tau^-(9/20)`
- `derivation`: `using |u1|<=M0 and |partial_z u1|<=C_u M0 tau^(-beta), |partial_z(u1^2)|<=2 C_u M0^2 tau^(-beta)`
- `closed`: `True`

## Comparisons

- `chosen_source_exponent`: `0.45`
- `chosen_source_exponent_fraction`: `9/20`
- `required_quadratic_bkm_source`: `tau^-2`
- `required_quadratic_bkm_exponent`: `2.0`
- `sprint130_source_proxy`: `tau^-1`
- `sprint130_source_proxy_exponent`: `1.0`
- `matches_required_quadratic_bkm_source`: `False`
- `dominates_required_quadratic_bkm_source`: `False`
- `bounded_by_sprint130_proxy_for_beta_le_one`: `True`
- `quadratic_source_obstructed`: `True`
- `comparison_note`: `the closed estimate is an upper bound at tau^(-beta), not a tau^-2 lower-source mechanism`

## Rows

| Gate | Expected | Actual | Passed | Evidence |
| --- | --- | --- | --- | --- |
| `Contract` | `ns_sprint131_source_upper_bound_audit` | `ns_sprint131_source_upper_bound_audit` | `True` | `deterministic Sprint131 audit emitting rows JSON, summary JSON, and Markdown` |
| `ReceiptLemma` | `PureDiffusionU1MaximumPrinciple` | `PureDiffusionU1MaximumPrinciple` | `True` | `{"accepted": true, "clay_navier_stokes_promoted": false, "complete": true, "contract": "ns_sprint130_u1_maximum_principle_audit", "exit_code": 0, "lemma": "PureDiffusionU1MaximumPrinciple", "linf_bound": "\|\|u1(t)\|\|_inf <= \|\|u1(0)\|\|_inf = M0", "source_path": "/home/c/Documents/code/dashi_agda/outputs/ns_sprint130_u1_maximum_principle_audit/ns_sprint130_u1_maximum_principle_audit_summary.json", "u1_linf_nonincreasing": true}` |
| `U1MaximumPrincipleInput` | `||u1(t)||_inf <= ||u1(0)||_inf = M0` | `||u1(t)||_inf <= ||u1(0)||_inf = M0` | `True` | `consumes and records the Sprint130 L-infinity receipt` |
| `ConcentrationScale` | `delta=tau^beta` | `delta=tau^9/20` | `True` | `beta is fixed deterministically inside the Sprint130 alpha window by default` |
| `SourceIdentity` | `partial_z(u1^2)=2 u1 partial_z u1` | `partial_z(u1^2)=2 u1 partial_z u1` | `True` | `product rule identity` |
| `DerivativeScale` | `|partial_z u1| <= C_u M0/delta = C_u M0 tau^(-beta)` | `|partial_z u1| <= C_u M0/delta = C_u M0 tau^(-beta)` | `True` | `receipt-level scaling upper bound` |
| `RigorousSourceUpperBound` | `|partial_z(u1^2)| <= C_source M0^2 tau^(-beta)` | `|partial_z(u1^2)| <= C_source M0^2 tau^(-beta)` | `True` | `using \|u1\|<=M0 and \|partial_z u1\|<=C_u M0 tau^(-beta), \|partial_z(u1^2)\|<=2 C_u M0^2 tau^(-beta)` |
| `QuadraticBkmComparison` | `tau^-2` | `tau^-(9/20)` | `True` | `{"bounded_by_sprint130_proxy_for_beta_le_one": true, "chosen_source_exponent": 0.45, "chosen_source_exponent_fraction": "9/20", "comparison_note": "the closed estimate is an upper bound at tau^(-beta), not a tau^-2 lower-source mechanism", "dominates_required_quadratic_bkm_source": false, "matches_required_quadratic_bkm_source": false, "quadratic_source_obstructed": true, "required_quadratic_bkm_exponent": 2.0, "required_quadratic_bkm_source": "tau^-2", "sprint130_source_proxy": "tau^-1", "sprint130_source_proxy_exponent": 1.0}` |
| `Sprint130ProxyComparison` | `tau^-1` | `tau^-(9/20)` | `True` | `for the selected beta<=1, tau^(-beta) is no more singular than tau^-1` |
| `ClayNavierStokesPromotion` | `false` | `false` | `True` | `this audit closes only RigorousSourceUpperBound and does not claim Clay Navier-Stokes` |
| `forbidden marker scan` | `zero hits` | `0` | `True` | `[]` |

## Control Card

- O: Worker 1 owns only the Sprint131 source upper-bound audit script and matching output directory
- R: close RigorousSourceUpperBound from the Sprint130 U1 maximum-principle receipt without Clay promotion
- C: deterministic Python audit consuming Sprint130 summary and emitting rows JSON, summary JSON, and Markdown
- S: Sprint130 L-infinity input, delta scale, product identity, derivative scale, and source upper bound all close
- L: the ledger records comparison against tau^-2 and tau^-1 source scales
- P: use the bound as an obstruction-class source upper bound, not as a quadratic source construction
- G: exit code is 0 exactly when all rows pass, source_upper_bound_closed is true, and Clay remains unpromoted
- F: missing Sprint130 receipt, failed scaling gate, marker hit, or Clay promotion fails closed
