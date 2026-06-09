# ns_sprint144_nonlocal_source_zero_number_failure

## Decision

- Decision: `fail_closed_nonlocal_source_zero_number_control_unavailable`
- Target gate: `ScalarZeroNumberTransferForVBarrier`
- Target variable: `v = partial_z u1`
- Missing theorem: `CoupledAxisymmetricZeroNumberForVBarrier`
- Missing comparison envelope: `ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators`
- Nonlocal source zero-number control: `False`
- Comparison envelope available: `False`
- Coupled zero-number theorem proved: `False`
- Secondary peak exclusion proved: `False`
- Global barrier closed: `False`
- Full Clay NS solved: `False`
- Clay Navier-Stokes promoted: `False`
- Artifact complete: `True`
- Invariants passed: `True`

## Equations

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Rows

| row_id | layer | status | failure mechanism | consequence |
| --- | --- | --- | --- | --- |
| sign_changing_partial_z2_psi1 | nonlocal_elliptic_source | sign_changing_source_uncontrolled | partial_z^2 psi1 is not globally signed; favorable local concavity near the main peak does not control all r-z points; the source can have the sign needed to raise v where the scalar template expects damping | The source term can move, preserve, or create axial sign changes; scalar zero-number monotonicity does not transfer. |
| off_peak_nonlocal_source | off_route_source_geometry | off_peak_source_hazard_open | elliptic feedback is not localized to the primary axial peak; off-route source mass can support a secondary positive shoulder; annular and boundary contributions are not excluded by local peak data | A secondary positive local maximum can remain compatible with the available ledgers, so zero-number transfer cannot exclude it. |
| radial_commutator_zero_creation | radial_transport_commutator | radial_commutator_unabsorbed | partial_r u1 is not controlled by an axial zero count; partial_z u^r is coupled to the global velocity field; the commutator can inject the wrong sign at an off-route crossing | Radial commutators can invalidate the scalar closed-equation hypothesis and can support new axial sign structure. |
| log_biot_savart_hazard | biot_savart_kernel | log_biot_savart_hazard_open | log amplification is compatible with the earlier hazard sampler; no log-aware commutator theorem is available; a local bounded ledger does not dominate unresolved near-coincident scales | The comparison budget can fail before a scalar zero-number contradiction is reached. |
| comparison_envelope_absent | comparison_interface | comparison_envelope_missing | no single residual inequality dominates partial_z^2 psi1 and commutators; constants are not shown compatible across radial, annular, and log hazards; the scalar equation used for comparison is not available | There is no certified scalar comparison problem whose zero-number decay can be imported into the coupled v dynamics. |
| secondary_peak_exclusion_unproved | barrier_gate | required_theorem_missing_fail_closed | the coupled zero-number theorem is not proved; secondary peak exclusion remains open; global barrier closure and Clay promotion are therefore blocked | The Sprint 144 lane must remain fail-closed and cannot promote the scalar zero-number route. |

## Control Card

- O: Worker lane 4 owns only scripts/ns_sprint144_nonlocal_source_zero_number_failure.py and outputs/ns_sprint144_nonlocal_source_zero_number_failure/.
- R: Record why nonlocal psi1 source and commutator terms break scalar zero-number transfer for v = partial_z u1.
- C: Deterministic Python ledger/sampler emitting summary JSON, row JSON, CSV, Markdown, and manifest through an atomic temp staging directory.
- S: partial_z^2 psi1 is sign-changing, off-peak source remains live, radial commutators and log Biot-Savart hazards are unabsorbed, and no comparison envelope is available.
- L: Scalar zero-number template -> nonlocal source gaps -> radial/log commutator gaps -> no comparison envelope -> no coupled theorem.
- P: Use as a fail-closed obstruction ledger only; do not use as a comparison proof or zero-number theorem.
- G: Validation passes only if all proof, envelope, barrier, Clay, and promotion flags remain false while artifact_complete is true.
- F: Missing: CoupledAxisymmetricZeroNumberForVBarrier and ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators; secondary peak exclusion, global barrier closure, and Clay Navier-Stokes promotion remain false.

## Governance

This artifact is fail-closed. It records why sign-changing partial_z^2 psi1, off-peak source, radial commutators, log Biot-Savart hazards, and the missing comparison envelope block scalar zero-number transfer.
