# Sprint 135 Corrected NS Status Assembly

Contract: `ns_sprint135_corrected_status_assembly`

Live NS boundary: `hou_luo_axisymmetric_with_swirl_open_candidate`

## Current State

- WBF exact tower intact: `true`
- Pure-u1 diffusion retracted: `true`
- Uniform no-log Biot-Savart lemma: `false`
- AXS viscous dominance obstruction retracted: `true`
- Hou-Luo axisymmetric with swirl open candidate: `true`

## Retracted And False

- Retracted claims: `PureDiffusionU1MaximumPrinciple, AxisymmetricHouLuoNSViscousDominanceObstruction`
- False lemmas: `NoLogAxisymmetricBiotSavartUniform`

## Rows

| row_id | mechanism_class | claim_or_result | current_status | status_kind |
| --- | --- | --- | --- | --- |
| wbf_exact_tower_intact | CLASS_WBF | WBF-L/WBF-S/WBF-MP/WBF-R | exact_unconditional_intact | preserved_result |
| pure_u1_diffusion_retracted | CLASS_AXS | PureDiffusionU1MaximumPrinciple | retracted_superseded | retracted_claim |
| swirl_circulation_gate_intact | CLASS_AXS | SwirlCirculationMaximumPrinciple | exact_replacement_gate_intact | replacement_gate |
| uniform_no_log_false | CLASS_AXS | NoLogAxisymmetricBiotSavartUniform | false_as_uniform_cylinder_lemma | false_lemma |
| axs_viscous_dominance_obstruction_retracted | CLASS_AXS | AxisymmetricHouLuoNSViscousDominanceObstruction | retracted | retracted_claim |
| hou_luo_axisymmetric_with_swirl_open | CLASS_AXS | HouLuoAxisymmetricNSWithSwirlRoute | open_live_candidate | live_boundary |
| full_clay_status_hold | FULL_3D_NS | ClayNavierStokesRegularity | not_solved_not_promoted | promotion_gate |

## Upstream Sprint 134 Summaries

`{"axisymmetric_equation_correction": true, "biot_savart_log_singularity_audit": true, "hou_luo_retraction_status": true}`

## Promotion

- `full_clay_ns_solved`: `false`
- `clay_navier_stokes_promoted`: `false`
- `complete`: `true`
