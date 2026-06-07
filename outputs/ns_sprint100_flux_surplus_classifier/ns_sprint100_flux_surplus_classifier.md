# NS Sprint 100 Flux Surplus Classifier

- Contract: `ns_sprint100_flux_surplus_classifier`
- Scope: deterministic flux-surplus source classification.
- Proof claimed: `false`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_FLUX_SURPLUS`
- Accepted source count: `0`
- Candidate family count: `6`
- Required gates: `signed_low_mode_flux_lower_bound`, `time_integrated_positive_surplus`, `beats_dissipation_budget`, `leray_energy_compatible`, `non_circular_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_flux_sign`, `target_kstar_collapse`, `imposed_surplus_window`
- Option B closed: `false`
- Clay Navier-Stokes promoted: `false`

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `T1` `signed_triadic_transfer` | triadic sign mechanism | `false` | `signed_low_mode_flux_lower_bound`, `time_integrated_positive_surplus`, `beats_dissipation_budget`, `non_circular_source`, `no_forbidden_dependency` | `imposed_flux_sign` | Triadic transfer is an admissible nonlinear channel, but the favorable sign is selected rather than derived and no time-integrated surplus is closed. |
| `S1` `shell_local_flux_surplus` | local shell flux channel | `false` | `signed_low_mode_flux_lower_bound`, `time_integrated_positive_surplus`, `beats_dissipation_budget` | `none` | Shell-local transfer is non-circular and energy-budget compatible, but it does not supply a signed lower bound or a comparison that beats dissipation. |
| `P1` `pressure_nonlocal_flux` | nonlocal pressure flux sketch | `false` | `signed_low_mode_flux_lower_bound`, `time_integrated_positive_surplus`, `beats_dissipation_budget` | `none` | Pressure coupling is compatible with incompressible Navier-Stokes, but the sketch lacks a quantitative signed surplus and a dissipation budget win. |
| `B1` `burst_integrated_surplus` | transient burst surplus | `false` | `signed_low_mode_flux_lower_bound`, `beats_dissipation_budget` | `none` | A burst can model a positive integral, but this family has no pointwise signed lower bound and does not close the dissipation comparison. |
| `I1` `inverse_cascade_surplus` | inverse-cascade surplus unsupported premise | `false` | `signed_low_mode_flux_lower_bound`, `time_integrated_positive_surplus`, `beats_dissipation_budget`, `leray_energy_compatible`, `non_circular_source`, `no_forbidden_dependency` | `target_kstar_collapse;desired_conclusion` | The surplus is tied to the desired cascade endpoint, so it supplies no independent source and remains outside a closed Leray-compatible budget. |
| `W1` `imposed_surplus_window` | imposed surplus interval | `false` | `leray_energy_compatible`, `non_circular_source`, `no_forbidden_dependency` | `imposed_surplus_window;desired_conclusion` | The window directly assumes the needed surplus and budget victory, so the mechanism is circular and uses a forbidden dependency. |

No candidate family satisfies every flux-surplus source gate without a forbidden dependency.
