# NS Sprint 144 R-Z Crossing Topology Sampler

- Contract: `ns_sprint144_rz_crossing_topology_sampler`
- Decision: `fail_closed_fixed_z_line_zero_count_insufficient`
- Target variable: `v = partial_z u1`
- Missing theorem: `CoupledRZZeroNumberFirstPositiveCrossingTheorem`
- Has scalar support: `true`
- Has r-z adverse topologies: `true`
- Fixed-line zero count sufficient: `false`
- Coupled zero-number theorem proved: `false`
- Secondary peak exclusion proved: `false`
- Global barrier closed: `false`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Artifact complete: `true`
- Invariants passed: `true`

## Rows

| row | topology | fixed delta | first r | first z | scalar support | r-z adverse | sufficient |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `fixed_line_decrease_support` | `scalar_fixed_line_support` | -2 | 1 | 0 | true | false | false |
| `radial_bypass_crossing` | `radial_bypass` | -2 | 1.42 | 0.18 | true | true | false |
| `annular_loop_crossing` | `annular_loop` | -2 | 2.15 | 0.31 | true | true | false |
| `saddle_node_pair_creation` | `saddle_node_zero_pair` | -2 | 1.26 | -0.22 | true | true | false |
| `boundary_interval_reentry` | `boundary_reentry` | -2 | 1.66 | 0.47 | true | true | false |

## Conclusion

The fixed z-line scalar zero count can decrease in every toy row, but this does not control the full r-z first positive crossing. Radial bypass, annular loop, saddle-node pair creation, and boundary interval reentry remain adverse topologies without the missing coupled theorem.

## Row Notes

- `fixed_line_decrease_support`: The fixed z-line scalar slice can show a decreasing zero count; this records local scalar support only.
- `radial_bypass_crossing`: The monitored fixed line improves, while the first positive crossing enters through a radial path outside that line.
- `annular_loop_crossing`: An annular loop can carry the first positive crossing around the controlled fixed z-line.
- `saddle_node_pair_creation`: A coupled r-z saddle-node pair can create an off-line positive region without increasing the chosen scalar slice count.
- `boundary_interval_reentry`: Boundary interval reentry leaves the fixed-line zero count compatible with an uncontrolled full-domain first crossing.

## Control Card

- O: Sprint 144 lane 3 owns only the r-z crossing topology sampler script and its generated output artifacts.
- R: Show by deterministic toy scenarios that fixed z-line scalar zero counts do not control full r-z first positive crossings.
- C: Pure Python stdlib; fixed rows; JSON, CSV, Markdown; robust temporary output directory replacement; no docs/tests/Agda edits.
- S: Scalar fixed-line decrease is recorded, while radial bypass, annular loop, saddle-node pair, and boundary reentry topologies remain adverse.
- L: Toy topology parameters -> fixed-line zero-count delta -> full r-z first crossing geometry -> missing theorem -> fail-closed flags.
- P: Do not promote: no coupled zero-number theorem, no secondary peak exclusion, no global barrier closure, and no Clay solution.
- G: Require has_scalar_support=true, has_rz_adverse_topologies=true, all proof/promotion flags false, artifact_complete=true, and invariants_passed=true.
- F: Any missing scenario, any sufficient fixed-line claim, any theorem proof, barrier closure, or Clay promotion fails the artifact.
