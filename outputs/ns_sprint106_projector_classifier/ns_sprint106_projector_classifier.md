# NS Sprint 106 Projector Source Classifier

- Contract: `ns_sprint106_projector_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_PROJECTOR_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `dyadic_partition`, `multiplier_boundedness`, `leray_compatibility`, `divergence_free_commutation`, `non_circular_construction`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `imposed_active_shell`, `imposed_frequency_support`, `non_leray_regularization`, `external_forcing`, `target_kstar_collapse`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `smooth_dyadic_cutoff` | `false` | `non_circular_construction`, `no_forbidden_dependency` | `desired_conclusion` | Smooth dyadic cutoffs are valid Leray-compatible multipliers, but they do not construct the active source without importing the target conclusion. |
| `sharp_frequency_annulus` | `false` | `multiplier_boundedness`, `non_circular_construction`, `no_forbidden_dependency` | `imposed_frequency_support` | The annulus names a frequency band, but sharp localization lacks the required bounded multiplier package and imposes the frequency support. |
| `heat_semigroup_projector` | `false` | `dyadic_partition`, `non_circular_construction`, `no_forbidden_dependency` | `non_leray_regularization` | Heat semigroup localization is bounded and divergence-free compatible, but the smoothing route is a regularization surrogate rather than a non-circular projector source. |
| `leray_lp_composed_projector` | `false` | `non_circular_construction`, `no_forbidden_dependency` | `target_kstar_collapse` | The Leray and Littlewood-Paley multipliers commute formally, but the construction becomes useful only after the target shell collapse is supplied. |
| `imposed_active_shell_projector` | `false` | `leray_compatibility`, `divergence_free_commutation`, `non_circular_construction`, `no_forbidden_dependency` | `imposed_active_shell;imposed_frequency_support;target_blowup;desired_conclusion` | The active shell and supporting frequencies are built into the input, so the candidate is circular and outside the unforced Leray projector source lane. |

No candidate supplies a dyadic partition, bounded multiplier package, Leray compatibility, divergence-free commutation, and non-circular construction while avoiding forbidden dependencies.
