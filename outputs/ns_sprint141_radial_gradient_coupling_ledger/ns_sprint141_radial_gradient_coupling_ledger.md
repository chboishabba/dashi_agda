# ns_sprint141_radial_gradient_coupling_ledger

## Decision

- Decision: `fail_closed_missing_radial_gradient_coupling`
- Target: `v = partial_z u1`
- Commutator: `-(partial_z u^r) partial_r u1`
- Missing theorem: `RadialGradientCouplingAtFirstAxialPositiveCrossing`
- Commutator sign-indefinite: `True`
- Global proof: `False`
- Clay promotion: `False`
- Validation passed: `True`

## Rows

| row_id | role | status | consequence |
| --- | --- | --- | --- |
| axial_crossing_geometry | first_positive_v_crossing | open_gap | The commutator sign is not fixed by the standard first-crossing maximum-principle ledger. |
| radial_slope_freedom | radial_gradient_counterledger | open_gap | The factor partial_r u1 remains free enough to flip the sign of -(partial_z u^r) partial_r u1 when partial_z u^r is nonzero. |
| gamma_max_principle_insufficiency | gamma_does_not_close_radial_slope | insufficient_input | Gamma control is insufficient to make the commutator favorable or dominated in the v barrier equation. |
| boundary_annulus_hazard | off_axis_and_boundary_hazard | open_hazard | The commutator remains a hazard outside any purely axial/local crossing argument. |
| missing_radial_gradient_coupling_theorem | promotion_blocker | required_theorem_missing | The v-barrier route cannot be globally promoted; the commutator is recorded as sign-indefinite pending the missing theorem. |

## Governance

This ledger is a blocker surface only. It validates absence of a global proof and absence of promotion; it does not supply the radial-gradient coupling theorem.
