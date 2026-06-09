# ns_sprint143_zero_number_obstruction

## Decision

- Decision: `fail_closed_zero_number_transfer_obstructed`
- Target gate: `SecondaryPeakExclusionForVBarrier`
- Target variable: `v = partial_z u1`
- Missing theorem: `CoupledAxisymmetricZeroNumberForVBarrier`
- Scalar zero-number transfer valid: `False`
- Coupled zero-number theorem available: `False`
- Secondary peak exclusion proved: `False`
- Global barrier closed: `False`
- Full Clay NS solved: `False`
- Clay promotion: `False`
- Artifact complete: `True`
- Invariants passed: `True`

## Equations

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Obstruction Rows

| row_id | layer | status | obstruction | consequence |
| --- | --- | --- | --- | --- |
| scalar_sturm_intuition_scope | scalar_template | transfer_invalid | v is coupled to u1, psi1, u^r, and u^z; the equation has nonhomogeneous source and transport-gradient terms; the scalar theorem's closed-order structure is absent | Scalar zero-number intuition is recorded as motivation only; it cannot be promoted into a transfer theorem for the v barrier. |
| coupled_rz_geometry_obstruction | geometry | coupled_geometry_open | radial derivatives influence the same maximum-principle ledger; axial zeros can move under radial diffusion and radial transport; a fixed z-line count does not control the full r-z first crossing | A one-dimensional sign-change count does not exclude a secondary positive v maximum in the coupled r-z barrier domain. |
| nonlocal_psi1_feedback | elliptic_feedback | nonlocal_feedback_uncontrolled | partial_z^2 psi1 is nonlocal and not globally signed; off-peak elliptic feedback can support secondary shoulders; known amplitude controls do not yield zero-count monotonicity | The source term can move or create axial sign changes outside the scalar zero-number template. |
| radial_transport_commutators | transport_commutator | commutator_gap_open | partial_r u1 is not fixed by axial first-crossing data; partial_z u^r is coupled nonlocally to the flow; commutator signs can oppose the desired barrier inequality | Radial transport and commutators prevent a direct Sturmian transfer from closing secondary peak exclusion. |
| moving_boundary_annulus | domain_geometry | annular_boundary_gap_open | first crossings may occur near annular or boundary layers; local axial counts do not determine boundary-compatible radial jets; moving localization can shift the relevant comparison interval | The scalar fixed-domain zero-count mechanism does not rule out secondary positive crossings in the annular barrier regime. |
| absent_constants | quantitative_interface | constants_absent | no numerical or analytic constants are supplied for the coupled theorem; no domination margin absorbs all source and commutator hazards; no compatibility proof ties zero-number decay to the global barrier | The ledger cannot close even a conditional quantitative transfer from scalar zero-number intuition. |
| missing_coupled_zero_number_theorem | required_theorem_interface | required_theorem_missing | CoupledAxisymmetricZeroNumberForVBarrier is not supplied; secondary peak exclusion remains unproved; the global barrier remains open | The Sprint 143 ledger remains fail-closed and cannot promote the Hou-Luo barrier route or Clay Navier-Stokes. |

## Control Card

- O: Worker lane 4 owns only scripts/ns_sprint143_zero_number_obstruction.py and outputs/ns_sprint143_zero_number_obstruction/.
- R: Record why scalar 1D Sturm/zero-number intuition does not directly close the coupled v-barrier route.
- C: Deterministic Python emitter producing summary JSON, row JSON, CSV, Markdown, and a manifest.
- S: All rows keep scalar transfer invalid, the coupled theorem unavailable, secondary peak exclusion unproved, and the global barrier open.
- L: Scalar 1D intuition -> coupled r-z and nonlocal feedback gaps -> commutator, annulus, and constants gaps -> missing theorem.
- P: Use this as an obstruction ledger only; do not treat it as a zero-number theorem or a barrier closure.
- G: Validation passes only if the fail-closed summary booleans and row-level proof/promotion flags stay false.
- F: Missing theorem: CoupledAxisymmetricZeroNumberForVBarrier; no global barrier closure, no full Clay Navier-Stokes solution, and no Clay promotion.

## Governance

This artifact is fail-closed. It records the missing coupled zero-number theorem and does not close secondary peak exclusion, the global barrier, or Clay Navier-Stokes.
