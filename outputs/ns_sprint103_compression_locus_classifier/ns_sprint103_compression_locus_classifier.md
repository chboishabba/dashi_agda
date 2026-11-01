# NS Sprint 103 Compression-Locus Geometry Classifier

- Contract: `ns_sprint103_compression_locus_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_COMPRESSION_LOCUS_GEOMETRY`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Required gates: `concentration_measure`, `compressive_strain_locus`, `eigenframe_alignment`, `colocation_estimate`, `leray_compatible`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_compression_sign`, `imposed_compression_locus`, `imposed_concentration_locus`, `imposed_colocation`, `imposed_compressive_locus`, `imposed_eigenframe_alignment`, `target_kstar_collapse`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `measured_concentration_locus` | `false` | `compressive_strain_locus`, `eigenframe_alignment`, `colocation_estimate`, `non_circular_source` | `none` | A concentration measure does not locate compressive low-mode strain or align the high-frequency energy tensor with that strain. |
| `low_strain_eigenvalue_barrier` | `false` | `concentration_measure`, `eigenframe_alignment`, `colocation_estimate`, `non_circular_source` | `none` | A compressive strain region alone does not show high-frequency energy concentrates there or in the compressive eigendirections. |
| `eigenframe_alignment_transport` | `false` | `eigenframe_alignment`, `colocation_estimate`, `non_circular_source`, `no_forbidden_dependency` | `imposed_eigenframe_alignment` | The needed eigenframe alignment is imposed at the step where it must be derived from unforced dynamics. |
| `vortex_tube_self_alignment` | `false` | `concentration_measure`, `eigenframe_alignment`, `colocation_estimate`, `non_circular_source`, `no_forbidden_dependency` | `desired_conclusion` | Vortex-tube geometry is compatible with the intended picture, but the self-alignment mechanism is not derived without the desired collapse geometry. |
| `imposed_colocation` | `false` | `leray_compatible`, `non_circular_source`, `no_forbidden_dependency` | `imposed_colocation;imposed_compressive_locus;desired_conclusion` | This builds the required colocation into the candidate and is therefore circular for the unforced Leray route. |

No candidate derives concentration, compressive strain, eigenframe alignment, and colocation from a non-circular Leray-compatible source.
