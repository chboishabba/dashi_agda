# NS Sprint 96 Collapse Scaling Sanity

- Contract: `ns_sprint96_collapse_scaling_sanity`
- Scope: deterministic sanity evaluation of candidate `K*(t)` collapse laws for Option B.
- Proof claimed: `false`
- Fail closed: `true`
- Accepted source count: `0`
- Candidate count: `4`
- Final decision: `FAIL_CLOSED`
- Required gates: `finite_time_collapse`, `leray_energy_compatible`, `excludes_conditional_lower_bound`, `singularity_extraction`, `no_forbidden_dependency`
- Forbidden dependencies: `clay_claim`, `target_absorption`, `desired_conclusion`, `h1_continuation`, `theta_preservation`, `option_c_conditional`, `conditional_regular`, `general_data_regular`, `blowup_construction_assumed`, `target_blowup`, `bkm_failure_assumed`, `serrin_failure_assumed`, `desired_singularity`, `negated_conditional_criterion_without_mechanism`

| Candidate | Law | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `C0` constant lower-bound | `K*(t) = K0 > 0 for 0 <= t < T` | `false` | `finite_time_collapse`, `excludes_conditional_lower_bound`, `singularity_extraction` | `none` | Compatible with a lower-bound picture but does not collapse to zero; it therefore cannot drive Option B. |
| `A1` algebraic collapse to 0 | `K*(t) = c (T - t)^alpha, alpha > 0` | `false` | `leray_energy_compatible`, `excludes_conditional_lower_bound`, `singularity_extraction` | `none` | Supplies a formal collapse rate, but this sanity ledger has no independent Leray-compatible construction, lower-bound exclusion, or singularity extraction. |
| `L1` logarithmic slow collapse | `K*(t) = c / log(e + 1/(T - t))` | `false` | `leray_energy_compatible`, `excludes_conditional_lower_bound`, `singularity_extraction` | `none` | A slower collapse ansatz still lacks an independent energy compatibility mechanism and does not defeat conditional lower-bound criteria. |
| `O1` oscillatory candidate | `K*(t) = c (T - t)^alpha (1 + beta sin(omega log(1/(T - t))))` | `false` | `leray_energy_compatible`, `excludes_conditional_lower_bound`, `singularity_extraction`, `no_forbidden_dependency` | `desired_singularity` | Oscillation adds no accepted extraction mechanism here and is rejected for relying on a target singularity dependency. |

The ledger is fail-closed because no candidate satisfies all required gates without a forbidden dependency.
