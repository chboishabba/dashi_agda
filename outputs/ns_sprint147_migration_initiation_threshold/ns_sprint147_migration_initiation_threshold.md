# Sprint 147 Migration Initiation Threshold

Deterministic fail-closed emitter for `MigrationInitiationThresholdForLargeData`.

## Decision

- decision: `fail_closed_migration_initiation_threshold_not_proved`
- target gate: `MigrationInitiationThresholdForLargeData`
- threshold proved: `false`
- blowup existence proved: `false`
- pure diffusion at symmetry plane: `true`
- maximum-location migration exclusion: `false`
- Clay promotion: `false`

## Rows

| row_id | status | observed | threshold | margin | blockers |
|---|---|---:|---:|---:|---|
| source_integral_threshold | THRESHOLD_NOT_REACHED | 0.82 | 1 | -0.18 | large_data_source_integral_lower_bound_missing, MaximumLocationMigrationLemma |
| symmetry_plane_diffusion_baseline | PURE_DIFFUSION_BASELINE_AVAILABLE | 1 | 1 | 0 |  |
| off_axis_gain | OFF_AXIS_GAIN_UNCONTROLLED | 1.34 | 1 | 0.34 | off_axis_gain_bound_missing, MaximumLocationMigrationLemma |
| viscosity_suppression | VISCOSITY_SUPPRESSION_PRESENT | 0.46 | 1 | -0.54 | uniform_viscous_retention_missing, large_data_scale_loss |
| log_supercritical_feedback | LOG_SUPERCRITICAL_FEEDBACK_OPEN | 1.72 | 1 | 0.72 | log_supercritical_feedback_absorption_missing |
| smooth_finite_energy_admissibility | ADMISSIBLE_BUT_NOT_PROOF | 1 | 1 | 0 | admissibility_does_not_imply_blowup, MaximumLocationMigrationLemma |
| clay_promotion_guard | PROMOTION_BLOCKED | 0 | 1 | -1 | migration_initiation_threshold_proved_false, blowup_existence_proved_false, full_clay_ns_solved_false |

## Interpretations

- `source_integral_threshold`: The source integral is the desired trigger, but the deterministic ledger records no lower bound strong enough to initiate migration.
- `symmetry_plane_diffusion_baseline`: At the symmetry plane the normalized row is pure diffusion; this is local baseline support, not an off-axis migration exclusion.
- `off_axis_gain`: Off-axis gain can exceed the symmetry-plane baseline, so the threshold cannot be promoted from the pinned-plane computation.
- `viscosity_suppression`: Large-data scaling suppresses the retained viscous damping, leaving the source threshold without a uniform absorption margin.
- `log_supercritical_feedback`: The log-supercritical feedback multiplier remains adverse and is not absorbed by the current threshold ledger.
- `smooth_finite_energy_admissibility`: Smooth finite-energy admissibility is compatible with the row set, but compatibility is not a migration threshold proof.
- `clay_promotion_guard`: The guard explicitly blocks Clay promotion because neither the migration threshold nor blowup existence has been proved.

## Control Card

- O: Lane 2 owns only the Sprint 147 Python emitter and outputs/ns_sprint147_migration_initiation_threshold/ artifacts for the migration-initiation threshold.
- R: Emit deterministic rows for source integral threshold, symmetry-plane diffusion baseline, off-axis gain, viscosity suppression, log-supercritical feedback, smooth finite-energy admissibility, and the Clay promotion guard.
- C: Single stdlib Python script writes rows JSON, CSV, summary JSON, Markdown, and manifest through an atomic staging directory.
- S: The ledger is fail-closed: the symmetry plane remains pure diffusion, but no migration-initiation threshold, blowup existence theorem, or Clay Navier-Stokes solution is proved.
- L: Normalize each row against a unit threshold, record threshold margins, and require all proof and promotion flags to remain false while the pure-diffusion baseline flag remains true.
- P: Use the artifact as a threshold evidence packet for the missing MigrationInitiationThresholdForLargeData gate, not as a proof.
- G: Validation passes only when all seven named rows exist, blockers are explicit, requested flags have the mandated truth values, and the artifact completeness invariant is true.
- F: Missing: a proved source-integral threshold, off-axis migration exclusion, blowup existence theorem, and Clay promotion eligibility.
