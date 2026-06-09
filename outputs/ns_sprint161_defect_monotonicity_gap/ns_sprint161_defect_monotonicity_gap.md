# Sprint 161 Defect Monotonicity Gap

- Decision: `fail_closed_general_3d_defect_monotonicity_gap`
- Fail closed: `True`
- Validation passed: `True`
- DefectMonotonicityForGeneral3D: `False`
- SymmetricHouLuoMachinerySupportsScopedRows: `True`
- General3DDefectMonotonicityGapOpen: `True`

## Local Defect Energy

D_r(t,x0) = normalized localized defect/enstrophy-energy excess on a parabolic ball Q_r(t,x0), compared against the scale-compatible dissipation and flux budget.

## Rows

| row_id | category | status | closed | sign | pressure | alignment | general_3d_gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| local_defect_energy_D_r | normalized_object | DEFINED_LEDGER_OBJECT_FAIL_CLOSED | False | A sign-definite localized flux/source inequality for D_r under scale-compatible cutoff errors. | Pressure decomposition with nonlocal tail controlled at the same scale as the localized defect budget. | Persistence of vortex-stretching alignment that prevents uncontrolled positive defect production. | The D_r object is normalized, but no monotone quantity is proved for arbitrary smooth finite-energy 3D data. |
| sign_hypothesis | needed_hypothesis | OPEN_FAIL_CLOSED | False | For all admissible cutoffs and centers, the combined local transport, vortex-stretching, and commutator remainder must be nonpositive after dissipation is charged. | Pressure must not reintroduce positive unbudgeted flux. | Alignment errors must be sign-compatible with the D_r budget. | General 3D vortex stretching has no sign in the current ledger, so D_r monotonicity cannot be promoted. |
| pressure_hypothesis | needed_hypothesis | OPEN_FAIL_CLOSED | False | The pressure contribution must be compatible with the sign ledger. | A local/nonlocal pressure split must bound pressure tails, harmonic leakage, and cutoff-gradient terms without losing critical scaling. | Alignment rows must absorb pressure-coupled stretching terms. | Pressure is nonlocal and can couple remote energy into Q_r; the current symmetric machinery does not exhaust that channel. |
| alignment_hypothesis | needed_hypothesis | OPEN_FAIL_CLOSED | False | Alignment must force the stretching source into the nonpositive ledger. | Pressure must preserve, not destroy, the alignment budget. | A stable cone/correlation condition must persist across scales and times for arbitrary 3D vorticity geometry. | No current artifact rules out adverse 3D vorticity geometry or loss of alignment under the full flow. |
| symmetric_machinery_support | support_boundary | SCOPED_SUPPORT_ONLY | True | Scoped sign reductions are available only under symmetric assumptions. | Scoped pressure handling is tied to the symmetric Hou-Luo packet. | Scoped alignment support is tied to axisymmetric/reflection structure. | Scoped support is not mechanism exhaustion for full 3D Navier-Stokes. |
| general_3d_open_gap | open_gap | OPEN_FAIL_CLOSED | False | Global-in-class sign-definite D_r inequality remains absent. | General nonlocal pressure closure remains absent. | General 3D alignment persistence remains absent. | Without the sign, pressure, and alignment hypotheses, D_r is a diagnostic ledger object rather than a monotone quantity for arbitrary 3D data. |

## Symmetric Machinery Boundary

The symmetric Hou-Luo packet supports scoped axisymmetric-with-swirl regularity rows. It does not close the sign, pressure, or alignment hypotheses needed for arbitrary 3D D_r monotonicity.

## Fail-Closed Summary Flags

- sign_hypothesis_missing: `True`
- pressure_hypothesis_missing: `True`
- alignment_hypothesis_missing: `True`
- general_3d_monotonicity_unproved: `True`
- symmetric_support_is_scoped_only: `True`
- full_clay_promotion_blocked: `True`

## O/R/C/S/L/P/G/F

- O: Lane 3 owns the Sprint161 defect-monotonicity gap emitter.
- R: Normalize the D_r monotonicity obstruction: local defect energy, needed sign/pressure/alignment hypotheses, symmetric support, and the remaining general 3D gap.
- C: One Python stdlib script writes JSON, CSV, Markdown, and manifest artifacts.
- S: Sprint157-160 isolate a symmetric Hou-Luo publication packet while keeping full Clay and mechanism-exhaustion promotion false.
- L: D_r monotonicity would need a closed local sign ledger, pressure control, and alignment persistence outside the symmetric class.
- P: Use this as a normalized obstruction ledger, not as a monotonicity theorem.
- G: Symmetric machinery can support scoped axisymmetric-with-swirl rows; general smooth finite-energy 3D Navier-Stokes remains guarded false.
- F: General 3D remains open because nonlocal pressure, vortex-stretching alignment, and sign-definite defect flux are not closed without the symmetry hypotheses.
