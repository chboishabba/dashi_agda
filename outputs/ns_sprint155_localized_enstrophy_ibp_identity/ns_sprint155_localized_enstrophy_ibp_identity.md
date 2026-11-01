# Sprint 155 Localized Enstrophy IBP Identity

## Decision

- Contract: `ns_sprint155_localized_enstrophy_ibp_identity`
- Decision: `identity_at_scale_delta_proved_route_assembly_fail_closed`
- Row count: `11`
- Localized identity at scale delta proved: `True`
- All route assembly rows closed: `False`
- Model validity for width ODE: `False`
- Symmetric Hou-Luo BKM finite: `False`
- Full Clay NS solved: `False`

## Identity

`d/dt E_delta + 2*nu*int phi_delta |grad omega_1|^2 = T_transport(phi_delta) + T_diff_cutoff(phi_delta) + T_stretch(phi_delta) + R_annulus(phi_delta) + B_wall(phi_delta)`

## O/R/C/S/L/P/G/F

- O: Worker 2 owns scripts/ns_sprint155_localized_enstrophy_ibp_identity.py and outputs/ns_sprint155_localized_enstrophy_ibp_identity/.
- R: Emit JSON/CSV/Markdown artifacts for the explicit localized omega_1 enstrophy IBP term ledger: time derivative, transport cutoff, diffusion coercivity, diffusion cutoff commutator, vortex stretching, annular leakage, wall term, near/far Biot-Savart support, constants, and model-validity status.
- C: One executable stdlib Python emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic output swap.
- S: The term-by-term IBP identity at fixed scale delta is closed as an algebraic ledger. Sprint 154 supplies route support for leakage, Biot-Savart, and constants. Downstream model-validity promotion is not made by this identity emitter.
- L: exact IBP row closure -> route assembly rows -> constants compatibility -> model validity for width ODE -> BKM guard -> Clay guard.
- P: Use this as the Sprint 155 identity ledger only. It is not a theorem that the width ODE follows from Navier-Stokes and it does not promote finite BKM or Clay Navier-Stokes.
- G: Validation requires all required row IDs, the localized identity flag true, model validity equal to all route assembly rows closed, and BKM plus Clay flags false.
- F: Missing: a separate model-validity promotion receipt, the finite symmetric Hou-Luo BKM translation, and the structurally separate full Clay Navier-Stokes mechanism-exhaustion theorem.

## Rows

| row_id | role | exact IBP | route closed | estimate status | support |
| --- | --- | --- | --- | --- | --- |
| time_derivative | identity_core | True | True | exact_identity_term_closed | active support of phi_delta |
| transport_cutoff | cutoff_transport | True | True | identity_term_closed_estimate_conditional | moving delta-annulus where derivatives of phi_delta are supported |
| diffusion_coercivity | diffusion_bulk | True | True | coercive_identity_term_closed | core plus cutoff support |
| diffusion_cutoff_commutator | diffusion_cutoff_error | True | True | identity_term_closed_absorption_open | delta-annulus and any cutoff transition adjacent to the wall |
| vortex_stretching_core | source_core | True | True | core_source_ledgered_estimate_open | localized omega_1/u_1 core |
| annular_leakage_residual | leakage_residual | True | True | closed_by_sprint152_domination_support | outer and inner annuli of the delta-localized cutoff |
| boundary_wall_term | wall_boundary | True | True | closed_by_wall_compatible_ibp_accounting | symmetry axis and physical wall boundary |
| near_biot_savart_support | velocity_support_near | True | True | near_support_localized_with_conditional_kernel_bound | near field around active core at scale delta |
| far_biot_savart_support | velocity_support_far | True | True | closed_by_sprint154_bkm_near_far_support | exterior vorticity and off-core annuli |
| constants_compatibility | constants_gate | True | True | closed_by_sprint154_simultaneous_constants_support | whole localized ledger |
| model_validity_status | model_guard | True | False | model_validity_false_until_all_route_rows_close | downstream width-ODE extraction |

## Guard

The fixed-scale localized omega_1 enstrophy IBP identity is recorded as proved. Sprint 154 route supports for annular leakage, near/far Biot-Savart, and simultaneous constants are recorded as closed. This emitter still does not promote model validity for the width ODE, finite symmetric Hou-Luo BKM, or full Clay Navier-Stokes.
