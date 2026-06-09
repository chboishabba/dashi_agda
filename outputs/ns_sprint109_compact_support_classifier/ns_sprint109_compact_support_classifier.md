# NS Sprint 109 Compact-Support Source Classifier

- Contract: `ns_sprint109_compact_support_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_COMPACT_SUPPORT_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `base_exp_smooth_function`, `boundary_flatness`, `compact_support_definition`, `smoothness_across_boundary`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `imposed_boundary_flatness`, `imposed_support_radius`, `external_forcing`, `target_kstar_collapse`, `non_leray_regularization`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `standard_exp_negative_inverse_bump` | `false` | `non_circular_source` | `none` | The exponential inverse profile supplies the usual smooth compact bump, but it does not derive a non-circular source for the closure argument. |
| `piecewise_polynomial_cutoff` | `false` | `base_exp_smooth_function`, `boundary_flatness`, `smoothness_across_boundary`, `non_circular_source`, `no_forbidden_dependency` | `imposed_support_radius` | The support interval is selected in advance, and a finite polynomial patch does not provide the required infinite-order flatness across the boundary. |
| `mollified_indicator_bump` | `false` | `base_exp_smooth_function`, `boundary_flatness`, `non_circular_source`, `no_forbidden_dependency` | `imposed_support_radius;non_leray_regularization` | Mollification gives a smoothened transition, but compact support comes from the selected indicator radius and the operation is a regularization input. |
| `imported_schwartz_cutoff` | `false` | `non_circular_source`, `no_forbidden_dependency` | `desired_conclusion` | The imported cutoff can meet the analytic shape checks, but its source use is asserted from the target conclusion rather than derived internally. |
| `imposed_compact_support_witness` | `false` | `non_circular_source`, `no_forbidden_dependency` | `imposed_boundary_flatness;imposed_support_radius;target_blowup;desired_conclusion` | This candidate has the requested formal labels only because the support radius, boundary flatness, and desired role are placed in the assumptions. |

No candidate supplies the base exponential smooth function, boundary flatness, compact-support definition, smoothness across the boundary, and a non-circular source while avoiding forbidden dependencies.
