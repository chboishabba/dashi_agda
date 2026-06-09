# Sprint 158 Assumption Scope Matrix

- Covered assumptions: `5`
- Out of scope rows: `3`
- Full Clay NS solved: `False`

| row_id | category | status |
| --- | --- | --- |
| smooth_hs_s_ge_3 | covered_assumption | COVERED |
| finite_energy | covered_assumption | COVERED |
| axisymmetric_with_swirl | covered_assumption | COVERED |
| z_reflection_symmetry | covered_assumption | COVERED |
| bounded_gamma | covered_assumption | COVERED |
| global_smooth_symmetric_solution | covered_conclusion | COVERED |
| unique_symmetric_solution | covered_conclusion | COVERED |
| publication_packet_ready | publication_surface | COVERED |
| general_3d_smooth_data | out_of_scope | OUT_OF_SCOPE_FAIL_CLOSED |
| mechanism_exhaustion | out_of_scope | OUT_OF_SCOPE_FAIL_CLOSED |
| clay_millennium_problem | out_of_scope | OUT_OF_SCOPE_FAIL_CLOSED |

## O/R/C/S/L/P/G/F

- O: Worker 3 owns the assumption/scope matrix.
- R: Separate covered assumptions, conclusions, documentary scope, and explicit non-claims.
- C: Python emitter writes matrix rows to JSON, CSV, Markdown, and manifest.
- S: The symmetric theorem is closed; general NS and Clay remain not covered.
- L: covered assumption -> covered conclusion -> documentary packet -> explicit non-claim.
- P: Use the matrix to prevent theorem-scope drift during publication.
- G: Any row marked out_of_scope must keep Clay/general NS flags false.
- F: Full Clay requires a mechanism-exhaustion theorem absent from this route.
