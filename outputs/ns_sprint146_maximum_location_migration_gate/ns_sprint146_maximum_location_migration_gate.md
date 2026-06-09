# Sprint 146 Maximum-Location Migration Gate

Deterministic fail-closed sampler for `MaximumLocationMigrationLemma`.

## Decision

- decision: `fail_closed_maximum_location_migration_gate_open`
- missing lemma: `MaximumLocationMigrationLemma`
- source sign formula: `source_sign = sign(2*u1*partial_z^2 psi1)`
- migration gate closed: `false`
- Clay promotion: `false`

## Rows

| row_id | status | source_sign | source | x_max_dot | blockers |
|---|---|---:|---:|---:|---|
| pinned_center | SUPPORT_LOCAL_ONLY | negative | -0.76 | 0 | MaximumLocationMigrationLemma, off_center_first_maximum_exclusion_missing |
| symmetric_twin_peak_migration | BLOCKED_BY_MAXIMUM_LOCATION_MIGRATION | negative | -0.1104 | -0.518333 | MaximumLocationMigrationLemma, tie_breaking_for_symmetric_twin_peaks_missing |
| positive_feedback_candidate | BLOCKED_BY_POSITIVE_SOURCE_FEEDBACK | positive | 0.4212 | 0.776585 | MaximumLocationMigrationLemma, ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators, positive_source_sign_not_absorbed |
| regularity_partial_recovery_branch | PARTIAL_RECOVERY_BLOCKED | positive | 0.0528 | -0.0611111 | MaximumLocationMigrationLemma, regularity_budget_does_not_supply_source_sign |

## Source Sign Logic

- `pinned_center`: u1 is positive and partial_z^2 psi1 is negative at the symmetry center, so 2*u1*partial_z^2 psi1 damps v locally.
- `symmetric_twin_peak_migration`: The pointwise source is weakly negative because partial_z^2 psi1 is weakly negative at each shoulder, but the spatial derivative of the source is nonzero, so the maximizing location can drift before a scalar maximum-principle argument closes.
- `positive_feedback_candidate`: u1 is positive and partial_z^2 psi1 is positive, so 2*u1*partial_z^2 psi1 reinforces v at the candidate maximum.
- `regularity_partial_recovery_branch`: Regularity keeps drift small, but the source sign is still determined by partial_z^2 psi1; a small positive value remains positive feedback.

## Control Card

- O: Lane 4 owns only Python sprint script/test surfaces and generated outputs/ns_sprint146_maximum_location_migration_gate/ artifacts for the Sprint 146 migration gate.
- R: Emit deterministic rows for pinned_center, symmetric_twin_peak_migration, positive_feedback_candidate, and regularity_partial_recovery_branch.
- C: Single stdlib Python sampler writes summary JSON, rows JSON, CSV, Markdown, and manifest through an atomic staging directory.
- S: The migration gate remains open: local pinned damping exists, but off-center migration, positive feedback, and partial regularity rows block closure.
- L: Compute source sign from 2*u1*partial_z^2 psi1, combine source-gradient and radial-drift proxies, classify migration status, then fail closed.
- P: Use the rows as a deterministic evidence packet for the missing MaximumLocationMigrationLemma rather than as a proof artifact.
- G: Validation passes only when all four named rows exist, source sign logic covers positive and negative branches, blockers are explicit, and all theorem/promotion flags remain false.
- F: Missing: MaximumLocationMigrationLemma; downstream comparison envelope, global barrier closure, and Clay promotion remain unavailable.
