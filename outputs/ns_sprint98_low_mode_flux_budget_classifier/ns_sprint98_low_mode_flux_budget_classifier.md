# NS Sprint 98 Low-Mode Flux Budget Classifier

- Contract: `ns_sprint98_low_mode_flux_budget_classifier`
- Scope: deterministic low-mode energy concentration mechanism classification.
- Proof claimed: `false`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_LOW_MODE_FLUX_BUDGET`
- Accepted source count: `0`
- Candidate family count: `6`
- Required gates: `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `leray_energy_budget_compatible`, `coherent_inverse_cascade`, `non_circular_kstar_forcing`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_inverse_cascade`, `target_kstar_collapse`
- Option B closed: `false`
- Clay Navier-Stokes promoted: `false`

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `F1` `direct_low_mode_forcing` | forced low-mode reservoir | `false` | `leray_energy_budget_compatible`, `coherent_inverse_cascade`, `non_circular_kstar_forcing`, `no_forbidden_dependency` | `external_forcing` | Direct injection can name a low-mode flux, but it is not an unforced Leray Navier-Stokes mechanism and uses forbidden external forcing. |
| `I1` `inverse_cascade_ansatz` | imposed inverse-cascade narrative | `false` | `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `leray_energy_budget_compatible`, `coherent_inverse_cascade`, `non_circular_kstar_forcing`, `no_forbidden_dependency` | `imposed_inverse_cascade;target_kstar_collapse` | A cascade direction asserted as an ansatz supplies no quantitative lower bound, residence estimate, or non-circular K* forcing. |
| `S1` `shell_local_transfer` | local shell transfer channel | `false` | `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `coherent_inverse_cascade`, `non_circular_kstar_forcing` | `none` | Local transfer is energy-budget compatible, but it does not force a sustained inverse cascade or produce a low-mode flux lower bound. |
| `P1` `pressure_nonlocal_transfer` | nonlocal coupling sketch | `false` | `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `coherent_inverse_cascade`, `non_circular_kstar_forcing` | `none` | Pressure nonlocality can be compatible with the equations, but the candidate lacks a signed quantitative flux lower bound and residence time. |
| `V1` `vortex_stretching_concentration` | stretching-to-concentration heuristic | `false` | `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `coherent_inverse_cascade`, `non_circular_kstar_forcing`, `no_forbidden_dependency` | `target_blowup` | Stretching is a valid nonlinear channel, but this family does not close the low-mode flux budget and relies on a target blowup endpoint. |
| `E1` `energy_transfer_ode` | formal low-mode ODE | `false` | `quantitative_low_mode_flux_lower_bound`, `residence_time_against_viscosity`, `coherent_inverse_cascade`, `non_circular_kstar_forcing`, `no_forbidden_dependency` | `desired_conclusion` | The ODE names the budget terms but leaves the required lower bound and anti-viscous residence estimate as assumptions. |

The classifier is fail-closed because no candidate family satisfies every low-mode flux budget gate without a forbidden dependency.
