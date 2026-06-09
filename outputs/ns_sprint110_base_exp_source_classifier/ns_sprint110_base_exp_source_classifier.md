# NS Sprint 110 Base Exponential Source Classifier

- Contract: `ns_sprint110_base_exp_source_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_BASE_EXP_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `exp_negative_inverse_seed`, `smoothness_on_positive_domain`, `derivative_hierarchy`, `positive_interior_nonzero`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `imposed_derivative_hierarchy`, `imposed_positive_interior`, `imported_bump_package`, `external_forcing`, `target_kstar_collapse`, `non_leray_regularization`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `classical_exp_negative_inverse_seed` | `false` | `derivative_hierarchy`, `non_circular_source` | `none` | The seed is smooth and positive on x > 0, but the full derivative hierarchy needed by the closure ledger is not derived, and no non-circular Navier-Stokes source is produced. |
| `reciprocal_power_exp_seed` | `false` | `exp_negative_inverse_seed`, `derivative_hierarchy`, `non_circular_source` | `none` | The reciprocal-power variant is smooth on the positive domain, but it is not the required exp(-1/x) seed and does not derive the hierarchy or a non-circular source. |
| `patched_exp_seed_with_declared_derivatives` | `false` | `smoothness_on_positive_domain`, `non_circular_source`, `no_forbidden_dependency` | `imposed_derivative_hierarchy` | The derivative ledger is declared rather than derived, the patching does not prove smoothness across the positive-domain construction, and the source role remains circular. |
| `imported_smooth_bump_seed` | `false` | `exp_negative_inverse_seed`, `non_circular_source`, `no_forbidden_dependency` | `imported_bump_package;desired_conclusion` | The smooth bump behavior is imported from an external package and specialized toward the desired conclusion, so it does not supply an internal non-circular base exponential source. |
| `imposed_base_exp_smooth_function` | `false` | `non_circular_source`, `no_forbidden_dependency` | `imposed_derivative_hierarchy;imposed_positive_interior;target_blowup;desired_conclusion` | The candidate has the requested analytic labels only because the hierarchy, interior positivity, and target role are imposed as assumptions. |

No candidate supplies the exp-negative-inverse seed, positive-domain smoothness, derivative hierarchy, positive interior nonzero witness, and a non-circular source while avoiding forbidden dependencies.
