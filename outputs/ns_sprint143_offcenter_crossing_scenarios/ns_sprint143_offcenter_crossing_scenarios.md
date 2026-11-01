# NS Sprint 143 Off-Center Crossing Scenarios

- Contract: `ns_sprint143_offcenter_crossing_scenarios`
- Blocker: `OffCenterFirstCrossingExclusion`
- Target variable: `v=partial_z u1`
- Route decision: `fail_closed_offcenter_crossings_admissible_no_promotion`
- Has centered support: `true`
- Has adverse scenarios: `true`
- Secondary peak exclusion proved: `false`
- Global barrier closed: `false`
- Clay Navier-Stokes promoted: `false`

## Rows

| row | geometry | source sign hazard | theorem requirement | centered support | adverse | admissible |
| --- | --- | --- | --- | --- | --- | --- |
| `centered_monotone_branch` | `centered_axis_monotone_first_crossing` | `none_local_centered_support_only` | `local_centered_monotone_support_not_global_theorem` | true | false | true |
| `small_offcenter_shoulder` | `small_offcenter_secondary_shoulder_first_crossing` | `offcenter_secondary_peak` | `SecondaryPeakExclusionForVCrossings` | false | true | true |
| `boundary_layer_crossing` | `near_boundary_layer_first_crossing` | `offcenter_secondary_peak+boundary_image_sign` | `BoundaryLayerCrossingExclusionOrSignedBoundaryKernelTheorem` | false | true | true |
| `annular_crossing` | `off_axis_annular_first_crossing` | `offcenter_secondary_peak+annular_kernel_sign` | `AnnularShoulderCrossingExclusionOrDominanceTheorem` | false | true | true |
| `delayed_crossing` | `time_delayed_offcenter_first_crossing` | `offcenter_secondary_peak+delayed_transport_sign` | `DelayedCrossingPersistenceExclusionTheorem` | false | true | true |

## Conclusion

The centered monotone branch is supported by this toy-profile classifier, but small off-center shoulder, boundary layer crossing, annular crossing, and delayed crossing rows remain admissible unless the listed theorem requirements are supplied.

## Row Notes

- `centered_monotone_branch`: The centered monotone branch is compatible with the local same-z support already sampled in Sprint 139/142.
- `small_offcenter_shoulder`: A small shoulder can move the first v crossing away from the centered monotone branch unless secondary peaks are excluded.
- `boundary_layer_crossing`: A boundary-layer crossing remains compatible with the toy ledger because boundary image/correction signs are unproved.
- `annular_crossing`: An annular crossing is not ruled out by centered monotonicity support without an annular shoulder exclusion theorem.
- `delayed_crossing`: A crossing delayed by transport can occur after the local centered window, so it needs a persistence/exclusion theorem.

## Control Card

- O: Sprint 143 lane 3 emits only the off-center crossing scenario classifier script and its generated output artifacts.
- R: Classify toy v=partial_z u1 crossing geometries: centered monotone support plus off-center, boundary-layer, annular, and delayed admissible scenarios.
- C: Pure Python stdlib; deterministic fixed toy rows; JSON, CSV, Markdown; no docs, tests, or Agda edits.
- S: Centered monotone branch is supported locally, but all adverse scenario classes remain admissible unless a theorem is supplied.
- L: toy profile parameters -> v crossing geometry -> source sign hazard -> theorem requirement -> fail-closed summary flags.
- P: Do not promote: no secondary-peak exclusion, no global barrier closure, and no Clay Navier-Stokes solution.
- G: Require has_centered_support=true, has_adverse_scenarios=true, all proof/promotion flags false, artifact_complete=true, and invariants_passed=true.
- F: Missing required rows, absent centered/adverse classes, any proof claim, missing constants closure, barrier closure, or Clay promotion fails closed.
