# Sprint 157 Symmetric Hou-Luo Regular Class Boundary

- SymmetricHouLuoBKMFinite: `True`
- SymmetricHouLuoRegularityClassClosure: `False`
- Full Clay NS solved: `False`

| row_id | category | status | note |
| --- | --- | --- | --- |
| smooth_hs_s_ge_3 | covered_assumption | COVERED | Smooth Sobolev data with s >= 3. |
| axisymmetric_with_swirl | covered_assumption | COVERED | Axisymmetric data with swirl in the Hou-Luo variables. |
| z_reflection_symmetry | covered_assumption | COVERED | z -> -z symmetry is preserved by the flow. |
| bounded_gamma | covered_assumption | COVERED | Gamma maximum principle provides time-uniform Umax input. |
| symmetric_hou_luo_bkm_finite | closed_result | COVERED | BKM finiteness closes the symmetric route. |
| theorem_level_class_statement | documentation_gap | OPEN_OR_OUT_OF_SCOPE | Publication-ready theorem prose still needs final statement. |
| general_three_dimensional_ns | out_of_scope | OPEN_OR_OUT_OF_SCOPE | General finite-energy 3D NS is not covered. |
| full_clay_mechanism_exhaustion | out_of_scope | OPEN_OR_OUT_OF_SCOPE | No exhaustion theorem for all mechanisms is present. |

## O/R/C/S/L/P/G/F

- O: Worker 4 owns the symmetric Hou-Luo regularity class boundary emitter.
- R: Normalize which initial-data assumptions are covered and which Clay-scale claims remain out of scope.
- C: Python ledger plus JSON, CSV, Markdown, and manifest outputs.
- S: Sprint157 BKM and continuation are closed for the symmetric axisymmetric-with-swirl route.
- L: assumption row -> covered class -> symmetric theorem closed -> class-statement doc still open -> full Clay separate.
- P: Use this as the exact publication-boundary ledger for the symmetric route.
- G: Do not strengthen to general smooth finite-energy 3D Navier-Stokes data.
- F: The remaining non-code item is theorem-level prose for SymmetricHouLuoRegularityClassClosure.
