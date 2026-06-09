# NS Sprint 113 Crow-Persistence Timescale Classifier

- Contract: `ns_sprint113_persistence_timescale_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_CROW_PERSISTENCE_TIMESCALE_SOURCE`
- Accepted source count: `0`
- Partial source count: `1`
- Candidate family count: `7`
- Initial-rate candidate partial: `true`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `leray_compatible_initial_data`, `initial_crow_dominance_imported`, `nonlinear_deformation_control`, `viscous_decay_window`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_blowup`, `desired_flux_surplus`, `imposed_persistence`, `imposed_alignment`, `external_forcing`, `numerical_only_evidence`, `target_kstar_collapse`, `hidden_smooth_continuation`

| Family | Verdict | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |
| --- | --- | --- | --- | --- | --- |
| `imported_thick_core_initial_rate` | `partial` | `false` | `nonlinear_deformation_control`, `viscous_decay_window`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window` | `none` | The imported thick-core initial-rate comparison is admissible as an initial witness, but it does not control nonlinear deformation, viscous decay, elliptic leakage, or a positive-flux accumulation window over a derived NSE timescale. |
| `linearized_crow_eigenmode_only` | `reject` | `false` | `nonlinear_deformation_control`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window`, `no_forbidden_dependency` | `imposed_persistence` | The linearized eigenmode can encode an initial Crow direction and a formal viscous damping scale, but nonlinear deformation and elliptic mode leakage are not controlled; persistence is inserted by the linear model rather than derived for unforced NSE. |
| `perturbative_short_time_smooth_solution` | `reject` | `false` | `viscous_decay_window`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window`, `no_forbidden_dependency` | `hidden_smooth_continuation` | Local smooth continuation can bound deformation only while the smooth solution is already available, and it supplies neither an explicit viscous decay window nor elliptic leakage control strong enough to force positive flux accumulation. |
| `energy_class_leray_only` | `reject` | `false` | `initial_crow_dominance_imported`, `nonlinear_deformation_control`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window` | `none` | The Leray energy class is admissible and dissipative, but the energy inequality alone does not import Crow dominance, resolve elliptic mode leakage, or give a lower bound for a positive-flux Crow window. |
| `externally_forced_persistence` | `reject` | `false` | `leray_compatible_initial_data`, `no_forbidden_dependency` | `external_forcing;imposed_persistence` | The timescale is maintained by an external driver and imposed persistence, so the mechanism is not an unforced Leray-data source for Crow persistence. |
| `numerical_crow_episode` | `reject` | `false` | `nonlinear_deformation_control`, `viscous_decay_window`, `elliptic_mode_leakage_control`, `persistence_timescale_lower_bound`, `positive_flux_accumulation_window`, `no_forbidden_dependency` | `numerical_only_evidence` | The simulated episode may display transient Crow geometry, but numerical-only evidence does not derive nonlinear deformation control, leakage bounds, or a rigorous persistence timescale lower bound for unforced NSE. |
| `target_flux_surplus_collapse` | `reject` | `false` | `leray_compatible_initial_data`, `nonlinear_deformation_control`, `viscous_decay_window`, `elliptic_mode_leakage_control`, `no_forbidden_dependency` | `desired_flux_surplus;imposed_persistence;target_kstar_collapse` | The candidate assumes the target collapse and desired flux surplus instead of deriving them from unforced NSE persistence estimates. |

No candidate simultaneously supplies Leray-compatible initial data, imported initial Crow dominance, nonlinear deformation control, a viscous decay window, elliptic mode leakage control, a persistence timescale lower bound, positive flux accumulation, and absence of forbidden dependencies.
