# NS Sprint 107 Cutoff-Partition Source Classifier

- Contract: `ns_sprint107_cutoff_partition_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_CUTOFF_PARTITION_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `radial_bump`, `annulus_cover`, `partition_identity`, `overlap_bound`, `non_circular_normalization`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `imposed_cutoff_support`, `imposed_partition_identity`, `external_forcing`, `target_kstar_collapse`, `non_leray_regularization`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `standard_radial_bump_partition` | `false` | `non_circular_normalization`, `no_forbidden_dependency` | `desired_conclusion` | The usual radial bump package supplies the formal partition checks, but its normalization is useful here only after the desired cutoff-source role is assumed. |
| `compact_annulus_partition` | `false` | `partition_identity`, `non_circular_normalization`, `no_forbidden_dependency` | `imposed_cutoff_support` | Compact annuli give a finite-overlap cover, but the exact identity and source-bearing support are not derived without imposing the cutoff support. |
| `heat_kernel_scale_partition` | `false` | `radial_bump`, `partition_identity`, `non_circular_normalization`, `no_forbidden_dependency` | `non_leray_regularization` | Heat-kernel differences provide smooth scale localization, but they are a regularization route rather than a radial bump partition with a closed identity. |
| `sharp_to_smooth_mollified_partition` | `false` | `partition_identity`, `overlap_bound`, `non_circular_normalization`, `no_forbidden_dependency` | `target_kstar_collapse` | Mollification removes sharp edges, but the exact partition identity and uniform overlap bound are not obtained without tuning to the target shell collapse. |
| `imposed_cutoff_partition` | `false` | `non_circular_normalization`, `no_forbidden_dependency` | `imposed_cutoff_support;imposed_partition_identity;target_blowup;desired_conclusion` | The candidate passes formal partition checks only by placing the support and identity in the hypotheses, so it is circular. |

No candidate supplies radial bump construction, annulus cover, exact partition identity, uniform overlap bound, and non-circular normalization while avoiding forbidden dependencies.
