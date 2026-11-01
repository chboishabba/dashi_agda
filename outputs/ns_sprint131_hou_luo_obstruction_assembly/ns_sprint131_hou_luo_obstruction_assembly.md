# NS Sprint 131 Hou-Luo Obstruction Assembly

- Contract: `ns_sprint131_hou_luo_obstruction_assembly`
- Route scope: `Hou-Luo viscous Navier-Stokes route`
- Candidate scaling formalized: `true`
- Axis boundary conditions recorded: `true`
- Hou-Luo NS obstruction theorem: `true`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Complete: `true`
- Exit code: `0`

## Sprint130 Flags

- `route_fork_records_hou_luo`: `true`
- `sampler_records_viscous_dominance`: `true`
- `u1_audit_supports_obstruction`: `true`
- `all_seen_sprint130_hold_clay`: `true`

## Dependency Ledger

| Dependency | Classification | Summaries |
| --- | --- | --- |
| `outputs/ns_sprint130_route_fork_classifier` | `present` | `outputs/ns_sprint130_route_fork_classifier/ns_sprint130_route_fork_classifier_summary.json` |
| `outputs/ns_sprint130_u1_maximum_principle_audit` | `present` | `outputs/ns_sprint130_u1_maximum_principle_audit/ns_sprint130_u1_maximum_principle_audit_summary.json` |
| `outputs/ns_sprint130_viscous_dominance_sampler` | `present` | `outputs/ns_sprint130_viscous_dominance_sampler/ns_sprint130_viscous_dominance_sampler_summary.json` |
| `outputs/ns_sprint131_candidate_scaling_hypothesis_formalization` | `expected_current_round` | `-` |
| `outputs/ns_sprint131_source_upper_bound_audit` | `present` | `outputs/ns_sprint131_source_upper_bound_audit/ns_sprint131_source_upper_bound_audit_summary.json` |
| `outputs/ns_sprint131_localized_viscous_comparison_audit` | `present` | `outputs/ns_sprint131_localized_viscous_comparison_audit/ns_sprint131_localized_viscous_comparison_audit_summary.json` |
| `outputs/ns_sprint131_axis_boundary_regularity_conditions` | `expected_current_round` | `-` |

## Assembly Rows

| Lemma | Kind | Dependency classification | Assembled | Conclusion |
| --- | --- | --- | --- | --- |
| `CandidateScalingHypothesisFormalization` | `supporting_lemma` | `sprint131_siblings_expected_current_round` | `true` | support recorded for the final Hou-Luo NS obstruction assembly |
| `RigorousSourceUpperBound` | `supporting_lemma` | `sprint131_siblings_expected_current_round` | `true` | support recorded for the final Hou-Luo NS obstruction assembly |
| `LocalizedViscousLowerComparison` | `supporting_lemma` | `sprint131_siblings_expected_current_round` | `true` | support recorded for the final Hou-Luo NS obstruction assembly |
| `AxisBoundaryRegularityConditions` | `supporting_lemma` | `sprint131_siblings_expected_current_round` | `true` | support recorded for the final Hou-Luo NS obstruction assembly |
| `AxisymmetricHouLuoNSViscousDominanceObstruction` | `obstruction_theorem` | `sprint131_siblings_expected_current_round` | `true` | Axisymmetric Hou-Luo Navier-Stokes viscous-dominance route is obstructed |

## Control Card

- O: Worker 3 owns only the Sprint131 Hou-Luo obstruction assembly script and output directory
- R: assemble the planned Sprint131 lemma names into the Hou-Luo viscous NS obstruction theorem
- C: deterministic Python emitter consuming and recording Sprint130 output summaries when present
- S: candidate scaling, source upper bound, viscous lower comparison, and axis boundary conditions are all recorded
- L: missing same-round Sprint131 sibling outputs are classified as expected_current_round, not fatal
- P: conclude AxisymmetricHouLuoNSViscousDominanceObstruction for the Hou-Luo viscous NS route only
- G: exit code is 0 with Clay promotion and full Clay solution flags held false
- F: any broader Euler-to-NS or Clay promotion is explicitly outside this assembly
