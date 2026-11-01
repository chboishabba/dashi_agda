# Sprint 158 Theorem Statement Closure

- SymmetricHouLuoRegularityClassClosure: `True`
- Full Clay NS solved: `False`

## Theorem Statement

For smooth finite-energy axisymmetric Navier-Stokes initial data with swirl, z-reflection symmetry, Sobolev regularity H^s for s >= 3, and bounded Gamma/circulation input, the symmetric Hou-Luo route has finite BKM integral on every finite time interval and therefore admits a unique global smooth solution within that symmetric class.

| row_id | category | status |
| --- | --- | --- |
| regularity_hs_s_ge_3 | assumption | CLOSED |
| finite_energy | assumption | CLOSED |
| axisymmetric_with_swirl | assumption | CLOSED |
| z_reflection_symmetry | assumption | CLOSED |
| bounded_gamma | assumption | CLOSED |
| finite_bkm_integral | input_theorem | CLOSED |
| continuation_bridge | input_theorem | CLOSED |
| global_smooth_solution_in_symmetric_class | conclusion | CLOSED |
| full_clay_ns | scope_guard | OPEN_FAIL_CLOSED |

## O/R/C/S/L/P/G/F

- O: Worker 2 owns the theorem statement closure emitter.
- R: Normalize the exact theorem statement and promote SymmetricHouLuoRegularityClassClosure.
- C: Python stdlib emitter writes theorem rows, JSON, CSV, Markdown, and manifest.
- S: Sprint157 closes BKM and continuation; only theorem-level class statement remained open.
- L: Sprint157 BKM finite -> theorem statement -> class closure true -> full Clay guard false.
- P: Use this as the publication theorem statement boundary for the symmetric class.
- G: No general 3D NS or Clay promotion is permitted from this class statement.
- F: The unresolved global gap is mechanism exhaustion for full Clay NS.
