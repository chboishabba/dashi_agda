# NS Sprint 108 Radial-Bump Source Classifier

- Contract: `ns_sprint108_radial_bump_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_RADIAL_BUMP_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `smooth_compact_support`, `radial_profile`, `nonnegative_bump`, `annular_difference`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `imposed_profile_support`, `imposed_partition_identity`, `external_forcing`, `target_kstar_collapse`, `non_leray_regularization`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `standard_exp_cutoff_bump` | `false` | `annular_difference`, `non_circular_source` | `none` | The classical bump has smooth compact support and positivity, but it is only a local profile; it does not derive the annular difference source. |
| `mollified_ball_indicator` | `false` | `annular_difference`, `non_circular_source`, `no_forbidden_dependency` | `imposed_profile_support` | Mollification supplies smoothness only after the support geometry is placed in the input, and the annular difference is not a derived source. |
| `gaussian_truncation_bump` | `false` | `annular_difference`, `non_circular_source`, `no_forbidden_dependency` | `non_leray_regularization` | The Gaussian profile is regularizing data, and compact support comes from a truncation rather than a non-circular Leray source. |
| `imported_partition_bump` | `false` | `nonnegative_bump`, `non_circular_source`, `no_forbidden_dependency` | `imposed_partition_identity;desired_conclusion` | The imported partition can express annular differences, but its identity and source role are assumed rather than derived for this classifier. |
| `imposed_radial_profile` | `false` | `non_circular_source`, `no_forbidden_dependency` | `imposed_profile_support;imposed_partition_identity;target_blowup;desired_conclusion` | This candidate passes the formal shape checks only by including the desired profile support and annular identity in the hypotheses. |

No candidate supplies smooth compact support, a radial profile, nonnegative bump data, annular difference, and a non-circular source while avoiding forbidden dependencies.
