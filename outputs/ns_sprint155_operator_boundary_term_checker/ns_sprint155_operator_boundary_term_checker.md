# Sprint 155 Operator Boundary Term Checker

This artifact checks the weighted `Ltilde` integration-by-parts ledger for radial measure `r dr dz`.
It is not a proof artifact, and all BKM/Clay promotion flags remain false.

## Decision

- decision: `fail_closed_weighted_ltilde_ibp_has_boundary_and_commutator_obligations`
- valid emitter output: `True`
- BKM false: `False`
- Clay false: `False`
- negative margin rows: `poincare_annular_absorption_gap, simultaneous_operator_constants`

## Numeric Budgets

- nu: `1`
- inner_radius: `1/64`
- outer_radius: `4`
- axial_half_height: `3`
- cutoff_thickness: `1/8`
- cutoff_gradient_bound: `2`
- cutoff_laplacian_bound: `6`
- cutoff_gradient_scale: `16`
- cutoff_gradient_scale_float: `16.0`
- cutoff_laplacian_scale: `384`
- cutoff_laplacian_scale_float: `384.0`
- trace_constant_wall: `9/4`
- poincare_constant_core: `16/25`
- young_epsilon_gradient: `1/8`
- young_dual_constant: `2`
- radial_log_span_outer_over_inner: `256`
- dissipation_reserve: `128`
- poincare_reserve: `40`
- wall_trace_reserve: `36`

## Rows

| row | status | sign | margin | theorem closed |
| --- | --- | --- | ---: | --- |
| divergence_form_weighted_ltilde | identity_recorded | neutral_identity_before_ibp | 0 | False |
| weighted_ibp_bulk_coercive_gradient | coercive | favorable_negative_dissipation | 128 | False |
| axis_boundary_r_zero_regularity | compatible | zero_by_axis_weight_and_regularity | 4 | False |
| radial_wall_outward_normal_sign | open_sign | requires_dirichlet_or_robin_dissipative_wall_sign | 15 | False |
| axial_wall_outward_normal_sign | open_sign | top_bottom_wall_flux_must_be_nonpositive_or_absorbed | 19 | False |
| cutoff_gradient_commutator_young_split | absorbed | indefinite_absorbed_by_young_gradient_split | 13 | False |
| cutoff_laplacian_commutator_budget | absorbed | adverse_zero_order_cutoff_leakage | 6 | False |
| radial_weight_derivative_no_extra_bad_term | compatible | weight_derivative_is_inside_divergence | 8 | False |
| poincare_core_absorption | absorbed | zero_order_core_absorbed_by_gradient | 52 | False |
| poincare_annular_absorption_gap | open_gap | requires_annular_mean_or_boundary_anchor | -25 | False |
| simultaneous_operator_constants | open_constants | requires_single_constant_pack | -8 | False |
| bkm_clay_guard | guard_false | no_promotion | 0 | False |

## Open Obligations

- Prove the radial and axial wall boundary signs or provide a trace absorption theorem tied to the wall model.
- Close the annular weighted Poincare row with a mean-zero condition, boundary anchor, or annular exclusion theorem.
- Package cutoff, trace, Young, viscosity, and Poincare constants into one simultaneous theorem.
- Supply a separate BKM/Clay promotion theorem before changing any promotion flag.

## Control Card

- O: Worker 3 owns only scripts/ns_sprint155_operator_boundary_term_checker.py and outputs/ns_sprint155_operator_boundary_term_checker/.
- R: Emit a checker for weighted Ltilde integration by parts in divergence form, radial measure r dr dz, boundary/wall signs, cutoff-gradient commutators, and Poincare absorption rows.
- C: One stdlib Python emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic output-directory replacement.
- S: The numeric sample has positive interior diffusion and several absorbed estimates, but wall sign certification, annular Poincare closure, and simultaneous theorem constants remain open.
- L: Divergence form -> weighted IBP -> boundary signs -> cutoff commutators -> Poincare absorption -> simultaneous constants -> BKM/Clay guard.
- P: Use this artifact as operator-boundary accounting only; do not cite it as analytic closure, finite BKM control, or a Clay Navier-Stokes proof.
- G: Promotion is blocked unless all required rows are theorem-closed and all fail-closed flags flip through a separate proof artifact.
- F: Missing: boundary-compatible sign theorem at walls, annular Poincare closure under the active cutoff family, simultaneous constants, and standard BKM/Clay translation.
