# NS Sprint 112 Thick-Core Crow-Regime Candidate Classifier

- Contract: `ns_sprint112_crow_regime_candidate_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_THICK_CORE_CROW_DOMINANCE_SOURCE`
- Accepted source count: `0`
- Partial source count: `1`
- Candidate family count: `6`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `divergence_free_leray_data`, `thick_core_ratio_delta_over_b_ge_half`, `initial_crow_over_elliptic_rate_dominance`, `compressive_eigenframe_alignment_source`, `persistence_under_nse`, `elliptic_backreaction_bound`, `finite_time_flux_surplus`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_blowup`, `desired_flux_sign`, `imposed_alignment`, `imposed_colocation`, `numerical_only_evidence`, `external_forcing`, `non_leray_regularization`, `target_kstar_collapse`

| Family | Verdict | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |
| --- | --- | --- | --- | --- | --- |
| `initial_rate_only_thick_core_vortex_pair` | `partial` | `false` | `compressive_eigenframe_alignment_source`, `persistence_under_nse`, `elliptic_backreaction_bound`, `finite_time_flux_surplus` | `none` | The thick-core pair can be Leray-compatible and supports an initial Crow-over-elliptic rate comparison, but it does not derive a compressive eigenframe alignment source, persistence under NSE, an elliptic backreaction bound, or finite-time flux surplus. |
| `thick_core_vortex_pair_with_prescribed_alignment` | `reject` | `false` | `compressive_eigenframe_alignment_source`, `persistence_under_nse`, `elliptic_backreaction_bound`, `finite_time_flux_surplus`, `no_forbidden_dependency` | `imposed_alignment;imposed_colocation` | The candidate selects the needed compression and eigenframe geometry by placement, so the alignment source is not derived and the NSE-persistent flux-surplus route remains open. |
| `non_leray_regularized_crow_wave_packet` | `reject` | `false` | `divergence_free_leray_data`, `persistence_under_nse`, `finite_time_flux_surplus`, `no_forbidden_dependency` | `non_leray_regularization` | The regularization changes the admissible problem and does not give a Leray-data source or NSE persistence for the claimed flux surplus. |
| `numerical_thick_core_crow_episode` | `reject` | `false` | `compressive_eigenframe_alignment_source`, `persistence_under_nse`, `elliptic_backreaction_bound`, `finite_time_flux_surplus`, `no_forbidden_dependency` | `numerical_only_evidence` | Numerical episodes may suggest a thick-core Crow window, but they do not supply analytic compressive alignment, persistence under NSE, elliptic backreaction control, or finite-time flux surplus. |
| `target_kstar_collapse_crow_ansatz` | `reject` | `false` | `divergence_free_leray_data`, `compressive_eigenframe_alignment_source`, `persistence_under_nse`, `elliptic_backreaction_bound`, `no_forbidden_dependency` | `desired_flux_sign;target_kstar_collapse` | The ansatz inserts the target shell collapse and flux sign directly, and therefore cannot be an independent thick-core Crow dominance source. |
| `externally_forced_crow_dominance_profile` | `reject` | `false` | `divergence_free_leray_data`, `no_forbidden_dependency` | `external_forcing` | The dominance interval is maintained by external forcing, so the candidate is not an unforced Leray-data mechanism for Clay-relevant Navier-Stokes closure. |

No candidate simultaneously derives Leray data, thick-core ratio delta over b at least one half, initial Crow-over-elliptic rate dominance, a compressive eigenframe alignment source, persistence under NSE, an elliptic backreaction bound, finite-time flux surplus, and absence of forbidden dependencies.
