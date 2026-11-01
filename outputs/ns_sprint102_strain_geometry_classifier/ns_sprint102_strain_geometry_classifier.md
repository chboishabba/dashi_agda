# NS Sprint 102 Strain Geometry Classifier

- Contract: `ns_sprint102_strain_geometry_classifier`
- Scope: deterministic geometric signed compression source classification.
- Proof claimed: `false`
- Fail closed: `true`
- Route decision: `FAIL_CLOSED_STRAIN_GEOMETRY_SOURCE`
- Accepted source count: `0`
- Candidate family count: `5`
- Required gates: `ll_lh_vanish`, `hh_strain_identity`, `concentration_locus_correlation`, `leray_compatible`, `non_circular_compression_gate`, `no_forbidden_dependency`
- Forbidden dependencies: `assumed_bkm_failure`, `assumed_serrin_failure`, `assumed_singularity`, `target_blowup`, `desired_conclusion`, `external_forcing`, `imposed_compression_sign`, `imposed_vortex_geometry`, `imposed_pressure_alignment`, `target_kstar_collapse`, `imposed_concentration_locus`
- Option B closed: `false`
- Clay Navier-Stokes promoted: `false`

## Compact O/R/C/S/L/P/G/F

- O: classify candidate geometric sign sources for strain-driven compression
- R: all six gates must pass, including a non-circular compression gate
- C: single deterministic Python ledger emitting JSON and Markdown
- S: five named candidate families evaluated in fixed order
- L: acceptance is the conjunction of gate_results plus the non-circular compression gate
- P: FAIL_CLOSED_STRAIN_GEOMETRY_SOURCE
- G: Option B remains open; Clay Navier-Stokes is not promoted
- F: all candidates are rejected with concrete failed gates or dependencies

| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |
| --- | --- | --- | --- | --- | --- |
| `V1` `vortex_core_compression` | geometric vortex-core compression narrative | `false` | `ll_lh_vanish`, `concentration_locus_correlation`, `non_circular_compression_gate`, `no_forbidden_dependency` | `imposed_vortex_geometry;imposed_compression_sign` | A vortex-core picture is geometrically suggestive, but the favorable compression orientation is selected rather than derived from the Leray solution. Low/low and low/high leakage is not eliminated, and the core locus is not correlated to concentration by an independent estimate. |
| `S1` `strain_energy_density_alignment` | strain-eigenframe alignment heuristic | `false` | `ll_lh_vanish`, `concentration_locus_correlation`, `non_circular_compression_gate`, `no_forbidden_dependency` | `desired_conclusion` | The high/high strain identity is compatible with the energy ledger, but large strain density alone does not determine eigenframe sign after projection. The alignment needed for compression is the conclusion to be proved. |
| `L1` `spectral_localization_geometry` | frequency-local geometric localization | `false` | `ll_lh_vanish`, `concentration_locus_correlation`, `non_circular_compression_gate`, `no_forbidden_dependency` | `target_kstar_collapse` | Spectral localization can isolate high/high terms in an identity, but it does not by itself force where physical concentration occurs or determine the sign of compression on that locus. |
| `P1` `pressure_mediated_alignment` | pressure-alignment sign assertion | `false` | `ll_lh_vanish`, `hh_strain_identity`, `concentration_locus_correlation`, `non_circular_compression_gate`, `no_forbidden_dependency` | `imposed_pressure_alignment` | Pressure is part of the Leray projection, but it is not a free signed geometric source. The candidate does not close the high/high strain identity or remove lower interaction leakage without imposing alignment. |
| `I1` `imposed_compression_locus` | forbidden imposed compression source | `false` | `leray_compatible`, `non_circular_compression_gate`, `no_forbidden_dependency` | `imposed_concentration_locus;imposed_compression_sign;desired_conclusion` | The candidate builds the needed locus and sign into the construction, so it is circular and not compatible with an unforced Leray solution route. |

No candidate family supplies a non-circular geometric compression source with LL/LH vanish, HH strain identity, concentration-locus correlation, Leray compatibility, and forbidden-dependency gates all closed.
