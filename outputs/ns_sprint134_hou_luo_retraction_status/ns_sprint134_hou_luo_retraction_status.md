# Sprint 134 Hou-Luo Retraction Status

Contract: `ns_sprint134_hou_luo_retraction_status`

Retracted theorem: `AxisymmetricHouLuoNSViscousDominanceObstruction`

Axisymmetric viscous dominance obstruction retracted:
`True`

Hou-Luo axisymmetric NS route status:
`open_live_candidate`

## Corrected Consequence

The previous obstruction relied on a uniform no-log axisymmetric Biot-Savart
bound and a pure-diffusion/source-bound treatment of `u1`.  The corrected
accounting uses the circulation maximum principle for
`Gamma = r u_theta = r^2 u1`, while the source remains
`partial_z(u1^2)=2 u1 partial_z u1`.  With the logarithmic strain loss restored,
the Gronwall factor can be super-polynomial in `1/tau`, equivalently
super-exponential in `log(1/tau)`, so the source may beat polynomial viscous
damping.

## Status Table

| row_id | result_or_claim | previous_status | corrected_status | action |
| --- | --- | --- | --- | --- |
| axs_hou_luo_viscous_dominance_retracted | AxisymmetricHouLuoNSViscousDominanceObstruction | claimed_conditional_obstruction | retracted | retract_theorem_not_promote |
| no_log_axisymmetric_biot_savart_uniform_false | NoLogAxisymmetricBiotSavartUniform | load_bearing_open_lemma | false_uniformly_in_cylinder | mark_false_as_uniform_statement |
| corrected_swirl_variable_maximum_principle_intact | SwirlCirculationMaximumPrinciple | u1_maximum_principle_claimed | gamma_maximum_principle_intact | replace_u1_gate_with_gamma_gate |
| corrected_source_gradient_log_gronwall | CorrectedHouLuoSourceGradientAccounting | source_bounded_by_polynomial_viscous_comparison | log_gronwall_can_overpower_polynomial_viscosity | invert_dominance_conclusion |
| wbf_exact_obstruction_tower_intact | WBF-L/WBF-S/WBF-MP/WBF-R | exact_unconditional | exact_unconditional_intact | preserve |
| hou_luo_axisymmetric_ns_route_open_live | HouLuoAxisymmetricNSRoute | claimed_obstructed_in_beta_gt_0_window | open_live_candidate | mark_open_neither_obstructed_nor_confirmed |

## Promotion

- `full_clay_ns_solved`: `False`
- `clay_navier_stokes_promoted`: `False`
- `complete`: `True`
