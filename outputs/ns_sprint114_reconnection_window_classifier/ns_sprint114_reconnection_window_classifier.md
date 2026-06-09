# NS Sprint 114 Reconnection-Window Classifier

- Contract: `ns_sprint114_reconnection_window_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_RECONNECTION_WINDOW_LOWER_BOUND_SOURCE`
- Accepted source count: `0`
- Partial source count: `2`
- Candidate family count: `7`
- Thin-core rate correction partial: `true`
- Elliptic backreaction partial: `true`
- Reconnection-window lower bound closed: `false`
- Clay Navier-Stokes promoted: `false`
- Clay: `false`
- Required gates: `thin_core_crow_dominance`, `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `positive_flux_accumulation`, `kstar_collapse_threshold`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_blowup`, `imposed_flux_surplus`, `imposed_reconnection_duration`, `hidden_regular_continuation`, `numerical_only_evidence`, `external_forcing`, `target_kstar_collapse`

| Family | Verdict | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |
| --- | --- | --- | --- | --- | --- |
| `thin_core_rate_correction` | `partial` | `false` | `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `positive_flux_accumulation`, `kstar_collapse_threshold` | `none` | The thin-core rate correction is admissible supporting evidence for initial Crow dominance, but it does not derive elliptic backreaction control, a viscous nonlinear window, positive flux accumulation, or a k-star collapse threshold. |
| `elliptic_backreaction_bound` | `partial` | `false` | `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `positive_flux_accumulation`, `kstar_collapse_threshold` | `none` | The elliptic backreaction estimate can support the initial comparison, but it is not a derived unforced NSE lower bound on reconnection duration and does not control nonlinear deformation or flux accumulation through collapse. |
| `linear_reconnection_episode` | `reject` | `false` | `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `nonlinear_deformation_control`, `positive_flux_accumulation`, `kstar_collapse_threshold`, `no_forbidden_dependency` | `imposed_reconnection_duration` | The linear episode supplies a formal decay scale but inserts the reconnection duration and omits elliptic backreaction, nonlinear deformation, positive flux accumulation, and k-star threshold closure. |
| `short_time_regular_continuation` | `reject` | `false` | `reconnection_window_lower_bound`, `viscous_decay_window`, `positive_flux_accumulation`, `kstar_collapse_threshold`, `no_forbidden_dependency` | `hidden_regular_continuation` | Local smooth continuation controls deformation only by assuming a regular interval already exists, and it does not derive the reconnection-window lower bound or the positive flux and k-star collapse gates. |
| `positive_flux_surplus_inserted` | `reject` | `false` | `thin_core_crow_dominance`, `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `no_forbidden_dependency` | `imposed_flux_surplus;imposed_reconnection_duration` | The candidate assumes the flux surplus and duration that the classifier is meant to source, so the apparent k-star threshold is not derived from unforced NSE estimates. |
| `numerical_reconnection_episode` | `reject` | `false` | `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `positive_flux_accumulation`, `kstar_collapse_threshold`, `no_forbidden_dependency` | `numerical_only_evidence` | Numerical timing can suggest a reconnection episode, but numerical-only evidence does not establish the analytic lower bound, elliptic backreaction control, or collapse threshold. |
| `target_kstar_collapse_assumption` | `reject` | `false` | `thin_core_crow_dominance`, `elliptic_backreaction_bound`, `reconnection_window_lower_bound`, `viscous_decay_window`, `nonlinear_deformation_control`, `no_forbidden_dependency` | `assumed_blowup;external_forcing;target_kstar_collapse` | The mechanism assumes blowup or target k-star collapse and relies on external forcing, so it cannot be accepted as an unforced reconnection-window source. |

No candidate simultaneously supplies thin-core Crow dominance, elliptic backreaction control, a reconnection-window lower bound, a viscous decay window, nonlinear deformation control, positive flux accumulation, a k-star collapse threshold, and absence of forbidden dependencies.
