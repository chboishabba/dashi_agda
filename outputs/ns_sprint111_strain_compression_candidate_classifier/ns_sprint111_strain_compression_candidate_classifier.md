# NS Sprint 111 Strain-Compression Candidate Classifier

- Contract: `ns_sprint111_strain_compression_candidate_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_STRAIN_COMPRESSION_CORRELATION_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `divergence_free_leray_compatible_data`, `compressive_low_mode_strain_locus`, `high_frequency_energy_concentration`, `eigenframe_alignment`, `persistent_positive_strain_contraction`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_blowup`, `assumed_bkm_failure`, `assumed_serrin_failure`, `target_kstar_collapse`, `desired_flux_sign`, `imposed_compressive_colocation`, `imposed_eigenframe_alignment`, `numerical_only_evidence`, `external_forcing`, `non_leray_regularization`

| Family | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |
| --- | --- | --- | --- | --- |
| `axisymmetric_vortex_ring_data` | `false` | `high_frequency_energy_concentration`, `eigenframe_alignment`, `persistent_positive_strain_contraction`, `non_circular_source` | `none` | The data can be divergence-free and unforced, but symmetry alone does not derive high-frequency energy concentration, eigenframe alignment, or persistent positive strain contraction from a non-circular source. |
| `anti_parallel_vortex_tube_pair` | `false` | `high_frequency_energy_concentration`, `eigenframe_alignment`, `persistent_positive_strain_contraction`, `non_circular_source`, `no_forbidden_dependency` | `imposed_compressive_colocation` | The pair identifies a compressive interaction region only by arranging the tubes there; it does not close high-frequency concentration or persistent contraction without imposed colocation. |
| `strained_shear_layer_packet` | `false` | `eigenframe_alignment`, `persistent_positive_strain_contraction`, `non_circular_source`, `no_forbidden_dependency` | `desired_flux_sign` | The packet can localize energy near a compressive low-mode locus, but the eigenframe alignment and positive contraction sign are selected toward the desired flux behavior rather than derived. |
| `numerically_observed_vortex_stretching` | `false` | `persistent_positive_strain_contraction`, `non_circular_source`, `no_forbidden_dependency` | `numerical_only_evidence` | The observed episodes may show transient alignment, but numerical-only evidence does not prove persistent positive strain contraction in the Leray class and cannot serve as the non-circular Clay source. |
| `imposed_colocation_ansatz` | `false` | `divergence_free_leray_compatible_data`, `non_circular_source`, `no_forbidden_dependency` | `imposed_compressive_colocation;imposed_eigenframe_alignment;target_kstar_collapse` | The target correlation is built into the ansatz, and the construction does not supply independent divergence-free Leray-compatible data or a non-circular source. |

No candidate simultaneously derives Leray-compatible data, a compressive low-mode strain locus, high-frequency concentration, eigenframe alignment, persistent positive strain contraction, and a non-circular source while avoiding forbidden dependencies.
