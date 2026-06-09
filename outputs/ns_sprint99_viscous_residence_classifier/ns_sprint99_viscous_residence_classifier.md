# NS Sprint 99 Viscous Residence Classifier

- Contract: `ns_sprint99_viscous_residence_classifier`
- Scope: deterministic residence-time and viscous damping defeat classification.
- Proof claimed: `false`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_VISCOUS_RESIDENCE`
- Accepted source count: `0`
- Candidate family count: `6`
- Required gates: `positive_residence_window`, `time_integrated_flux_surplus`, `beats_viscous_damping`, `leray_energy_compatible`, `non_circular_kstar_collapse_forcing`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_residence_time`, `target_kstar_collapse`
- Option B closed: `false`
- Clay Navier-Stokes promoted: `false`

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `R1` `persistent_low_mode_reservoir` | reservoir without flux surplus closure | `false` | `time_integrated_flux_surplus`, `beats_viscous_damping`, `non_circular_kstar_collapse_forcing`, `no_forbidden_dependency` | `desired_conclusion` | A persistent reservoir names the desired state, but it does not derive the signed time-integrated surplus or an independent viscous defeat. |
| `B1` `burst_flux_window` | transient burst without residence control | `false` | `positive_residence_window`, `beats_viscous_damping`, `non_circular_kstar_collapse_forcing` | `none` | A burst can supply a formal flux surplus, but the candidate lacks a positive residence window and a closed comparison against viscosity. |
| `I1` `inverse_cascade_residence` | cascade residence postulate | `false` | `time_integrated_flux_surplus`, `beats_viscous_damping`, `leray_energy_compatible`, `non_circular_kstar_collapse_forcing`, `no_forbidden_dependency` | `target_kstar_collapse` | The residence interval is tied to the target K* collapse and supplies no non-circular flux surplus or Leray-compatible construction. |
| `P1` `pressure_trapping` | pressure trapping sketch | `false` | `positive_residence_window`, `time_integrated_flux_surplus`, `beats_viscous_damping`, `non_circular_kstar_collapse_forcing` | `none` | Pressure nonlocality is compatible with the equations, but this sketch does not yield a signed residence window or damping-defeat inequality. |
| `V1` `vortex_stretching_residence` | stretching residence heuristic | `false` | `positive_residence_window`, `time_integrated_flux_surplus`, `beats_viscous_damping`, `non_circular_kstar_collapse_forcing`, `no_forbidden_dependency` | `target_blowup` | Stretching is a real nonlinear channel, but this family assumes a blowup endpoint and does not close the residence or damping gates. |
| `T1` `imposed_residence_interval` | imposed interval | `false` | `time_integrated_flux_surplus`, `leray_energy_compatible`, `non_circular_kstar_collapse_forcing`, `no_forbidden_dependency` | `imposed_residence_time;desired_conclusion` | The interval is imposed rather than derived, so the damping defeat is not an admissible independent mechanism. |

No candidate family satisfies every residence-time and viscous damping gate without a forbidden dependency.
