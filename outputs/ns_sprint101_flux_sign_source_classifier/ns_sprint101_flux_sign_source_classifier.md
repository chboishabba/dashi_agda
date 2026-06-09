# NS Sprint 101 Flux Sign Source Classifier

- Contract: `ns_sprint101_flux_sign_source_classifier`
- Scope: deterministic signed low-mode flux lower-bound source classification.
- Proof claimed: `false`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_FLUX_SIGN_SOURCE`
- Accepted source count: `0`
- Candidate family count: `6`
- Required gates: `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting`, `leray_energy_compatible`, `non_circular_flux_sign_source`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_flux_sign`, `imposed_triad_phase`, `target_kstar_collapse`, `imposed_surplus_window`
- Option B closed: `false`
- Clay Navier-Stokes promoted: `false`

## Compact O/R/C/S/L/P/G/F

- O: classify candidate signed low-mode flux lower-bound mechanisms
- R: all seven gates must pass and forbidden dependencies must be absent
- C: single deterministic Python ledger emitting JSON and Markdown
- S: six named candidate families evaluated in fixed order
- L: acceptance is the conjunction of gate_results
- P: FAIL_CLOSED_FLUX_SIGN_SOURCE
- G: Option B remains open; Clay Navier-Stokes is not promoted
- F: all candidates are rejected with concrete failed gates or dependencies

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `T1` `coherent_triad_alignment` | phase-selected triadic sign sketch | `false` | `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting`, `non_circular_flux_sign_source`, `no_forbidden_dependency` | `imposed_triad_phase;imposed_flux_sign` | A favorable triad orientation is selected rather than derived; the candidate lacks a cancellation-defect bound and does not account for pressure transport in the projected low-mode budget. |
| `S1` `shell_local_sign_bias` | shell-local sign-bias heuristic | `false` | `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting` | `none` | Shell locality is compatible with the Leray energy ledger, but locality does not determine the sign after summing interacting triads and projected cancellations remain uncontrolled. |
| `P1` `pressure_projection_sign` | pressure-projection sign assertion | `false` | `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting` | `none` | The pressure projection is part of the equations, but it is not a signed source by itself; the candidate does not separate pressure transport from nonlinear transfer or bound the residual cancellation defect. |
| `H1` `helical_alignment_sign` | helical sign-alignment mechanism | `false` | `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting`, `non_circular_flux_sign_source`, `no_forbidden_dependency` | `imposed_triad_phase;desired_conclusion` | Helical decomposition can expose transfer channels, but the persistent alignment is imposed as the desired sign conclusion and is not propagated by a closed Leray-compatible mechanism. |
| `B1` `intermittent_burst_sign` | transient burst sign narrative | `false` | `triadic_sign_coherence`, `low_mode_projection_sign_control`, `cancellation_defect_bound`, `pressure_transport_sign_accounting`, `no_forbidden_dependency` | `imposed_surplus_window` | A burst interval can be named, but the signed window is imposed rather than derived and no uniform lower bound survives cancellation across the low-mode projection. |
| `F1` `imposed_flux_orientation` | forbidden imposed sign source | `false` | `cancellation_defect_bound`, `pressure_transport_sign_accounting`, `leray_energy_compatible`, `non_circular_flux_sign_source`, `no_forbidden_dependency` | `imposed_flux_sign;external_forcing;desired_conclusion` | The candidate directly prescribes the needed sign orientation, so any apparent sign control is circular and outside the unforced Navier-Stokes closure target. |

No candidate family supplies a non-circular signed low-mode flux lower-bound source with all required sign, cancellation, pressure-accounting, Leray, and dependency gates closed.
