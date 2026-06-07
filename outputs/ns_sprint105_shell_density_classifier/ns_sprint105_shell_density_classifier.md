# NS Sprint 105 Shell-Density Source Classifier

- Contract: `ns_sprint105_shell_density_classifier`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_SHELL_DENSITY_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Clay Navier-Stokes promoted: `false`
- Required gates: `lp_projector`, `local_density_definition`, `leray_integrability`, `localization_bound`, `non_circular_construction`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_density_locus`, `imposed_shell_energy`, `target_kstar_collapse`

| Family | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- |
| `lp_projector_density` | `false` | `localization_bound`, `non_circular_construction`, `no_forbidden_dependency` | `desired_conclusion` | The Littlewood-Paley projector supplies a formal shell energy density, but the needed localized lower-bound mechanism is not derived independently. |
| `mollified_local_energy_density` | `false` | `lp_projector`, `localization_bound`, `non_circular_construction` | `none` | Mollification is Leray-compatible and defines a local density, but it does not isolate a dyadic shell source or close the localization bound. |
| `dyadic_square_function_density` | `false` | `localization_bound`, `non_circular_construction`, `no_forbidden_dependency` | `target_kstar_collapse` | Square functions organize dyadic energy, but converting that ledger into the target localized shell source relies on the collapse endpoint. |
| `weak_leray_density_extraction` | `false` | `local_density_definition`, `localization_bound`, `non_circular_construction`, `no_forbidden_dependency` | `assumed_singularity` | Weak compactness can pass to subsequential energy distributions, but it does not construct a local shell density source without assuming a singular endpoint. |
| `imposed_shell_density` | `false` | `leray_integrability`, `non_circular_construction`, `no_forbidden_dependency` | `imposed_density_locus;imposed_shell_energy;desired_conclusion` | The candidate builds the needed density locus and shell energy into the construction, so any apparent bound is circular. |

No candidate derives a shell-local density, Leray integrability, localization bound, and non-circular construction while avoiding forbidden dependencies.
