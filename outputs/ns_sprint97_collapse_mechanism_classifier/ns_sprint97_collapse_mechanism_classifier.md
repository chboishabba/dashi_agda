# NS Sprint 97 Collapse Mechanism Classifier

- Contract: `ns_sprint97_collapse_mechanism_classifier`
- Scope: deterministic classification of candidate K* collapse mechanism families.
- Proof claimed: `false`
- Fail closed: `true`
- Accepted source count: `0`
- Candidate family count: `6`
- Final decision: `FAIL_CLOSED`
- Required gates: `finite_time_kstar_to_zero`, `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `blowup_construction_assumed`, `clay_claim`, `conditional_regular_negation`, `desired_conclusion`, `h1_continuation_failure_assumed`, `option_c_lower_bound_negated_without_mechanism`, `self_similarity_imposed_as_proof`, `target_absorption`, `target_blowup`

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `C0` constant lower bound | non-collapse lower-bound family | `false` | `finite_time_kstar_to_zero`, `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin` | `none` | This family preserves a positive K* floor, so it cannot supply finite-time K* collapse or exclude the lower-bound alternative. |
| `A1` pure algebraic collapse | rate ansatz without dynamics | `false` | `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin` | `none` | The rate tends to zero but supplies no independent concentration dynamics, viscous defeat estimate, Leray trajectory, or singularity extraction. |
| `L1` logarithmic collapse | slow rate ansatz without dynamics | `false` | `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin` | `none` | The logarithmic profile is still only a prescribed rate; it does not derive the required energy-transfer and damping gates. |
| `O1` oscillatory ansatz | oscillatory rate ansatz | `false` | `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin`, `no_forbidden_dependency` | `assumed_singularity` | Oscillation does not provide a closed low-mode transfer mechanism and relies on the singular endpoint as an input. |
| `S1` imposed self-similar ansatz | imposed self-similar profile | `false` | `low_mode_energy_concentration_dynamics`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin`, `no_forbidden_dependency` | `self_similarity_imposed_as_proof;target_blowup` | A profile imposed at the outset is not an extracted Leray-compatible trajectory and is rejected as a forbidden dependency. |
| `E1` energy-transfer ODE sketch | formal transfer sketch | `false` | `finite_time_kstar_to_zero`, `viscous_damping_defeat_estimate`, `leray_compatible_trajectory`, `excludes_option_c_lower_bound`, `singularity_extraction_without_bkm_or_serrin`, `no_forbidden_dependency` | `target_absorption` | The ODE sketch names a transfer channel but lacks a quantitative damping defeat estimate, K* collapse law, Leray construction, and extraction bridge. |

The classifier is fail-closed because no mechanism family satisfies every required gate without a forbidden dependency.
