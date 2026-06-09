# Sprint 153 Localized Vortex-Stretching Source

- Gate: `LocalizedCoreVortexStretchingSourceForOmega1`
- Decision: `core_source_bound_shape_recorded_as_evidence_fail_closed`
- Generic shape: `core_source <= C*u1*v*Omega*delta^2`
- Canonical evidence: `core_source <= 2*u1*v*Omega*delta^2`
- Invariant valid: `True`
- Clay promoted: `False`

## O/R/C/S/L/P/G/F

- O: Worker 2 owns scripts/ns_sprint153_localized_vortex_stretching_source.py and outputs/ns_sprint153_localized_vortex_stretching_source/.
- R: Normalize the localized omega1 vortex-stretching core source as evidence for the bound shape core_source <= C*u1*v*Omega*delta^2, including the canonical 2*u1*v*Omega*delta^2 bookkeeping row.
- C: A stdlib Python emitter writes a JSON ledger, CSV ledger, summary JSON, Markdown report, and manifest through an atomic directory replacement.
- S: The model source term 2*u1*partial_z u1 is localized on a delta-core; using |partial_z u1| <= v*Omega and a normalized core-ball area factor gives the evidence shape 2*u1*v*Omega*delta^2.
- L: Rows cover source input, core ball, cutoff support, sign, constants, dimensional scaling, and theorem flags; promotion is lower than any analytic theorem and is explicitly blocked.
- P: Use the artifact as deterministic evidence for the symbolic bound shape only; it must be followed by rigorous cutoff, sign, uniform-constant, localized-identity, and model-validity theorems.
- G: Validation requires all eight rows, the exact bound strings, canonical constant 2, delta exponent 2, positive evidence rows, and every theorem or Clay flag false.
- F: No theorem is proved: sign-definiteness, cutoff support, uniform constants, dimensional theorem status, localized identity closure, finite BKM, and Clay NS remain open.

## Ledger

| row_id | category | status | coefficient | delta_power | theorem_flag |
| --- | --- | --- | ---: | ---: | --- |
| omega1_equation_source_input | source_input | RECORDED_EVIDENCE_ONLY | 2 | 0 | False |
| core_ball_volume_scale | core_ball | SUPPORTS_DELTA_SQUARE_SCALE | 1 | 2 | False |
| localized_core_source_bound | core_source | DERIVED_SYMBOLIC_EVIDENCE | 2 | 2 | False |
| cutoff_support_gate | cutoff_support | SUPPORT_RECORDED_NOT_PROVED | 4 | 2 | False |
| source_sign_orientation | sign | FAIL_CLOSED_SIGN_NOT_PROMOTED | 2 | 2 | False |
| constant_normalization | constants | CANONICAL_CONSTANT_RECORDED | 2 | 2 | False |
| dimensional_scaling_delta_square | dimensional_scaling | DIMENSIONAL_SHAPE_CONSISTENT | 2 | 2 | False |
| fail_closed_theorem_flags | governance | FAIL_CLOSED | 0 | 2 | False |

## Guard

This artifact records the localized core-source bound shape as deterministic evidence only. It does not prove the omega1 theorem, localized identity, finite BKM, or Clay Navier-Stokes.
