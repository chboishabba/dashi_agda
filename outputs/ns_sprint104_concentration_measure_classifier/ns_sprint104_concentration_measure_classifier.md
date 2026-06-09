# NS Sprint 104 Concentration-Measure Source Classifier

- Contract: `ns_sprint104_concentration_measure_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_CONCENTRATION_MEASURE_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Required gates: `dyadic_energy_density`, `threshold_selection`, `locus_measurability`, `scale_local_tightness`, `leray_compatible`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_concentration_locus`, `imposed_concentration_measure`, `imposed_defect_measure`, `imposed_high_frequency_threshold`, `imposed_intermittency_profile`, `maximal_locus_as_source`, `target_kstar_collapse`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `shell_energy_density_threshold` | `false` | `threshold_selection`, `scale_local_tightness`, `non_circular_source`, `no_forbidden_dependency` | `imposed_high_frequency_threshold` | The dyadic density is available, but the threshold needed to isolate concentration is not selected from a non-circular Leray budget. |
| `maximal_function_locus` | `false` | `scale_local_tightness`, `non_circular_source`, `no_forbidden_dependency` | `maximal_locus_as_source` | A maximal-function superlevel set is measurable, but it repackages concentration instead of deriving a scale-local source for it. |
| `defect_measure_extraction` | `false` | `threshold_selection`, `scale_local_tightness`, `non_circular_source`, `no_forbidden_dependency` | `imposed_defect_measure` | Weak compactness can name a defect, but it does not provide a non-circular threshold or tight scale-local production mechanism. |
| `intermittency_profile_measure` | `false` | `scale_local_tightness`, `leray_compatible`, `non_circular_source`, `no_forbidden_dependency` | `imposed_intermittency_profile;desired_conclusion` | The intermittency profile supplies the desired concentration geometry as an ansatz rather than deriving it inside the unforced Leray class. |
| `imposed_concentration_locus` | `false` | `leray_compatible`, `non_circular_source`, `no_forbidden_dependency` | `imposed_concentration_locus;imposed_concentration_measure;desired_conclusion` | This candidate passes formal measurement checks only by building the concentration locus into the input data. |

No candidate derives dyadic density, threshold selection, measurable locus, and scale-local tightness from a non-circular Leray-compatible source.
