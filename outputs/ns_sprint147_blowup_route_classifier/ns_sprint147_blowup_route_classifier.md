# Sprint 147 Blowup Route Classifier

## Decision

- Contract: `ns_sprint147_blowup_route_classifier`
- Decision: `classify_post_sprint146_blowup_routes_fail_closed`
- State basis: `post_sprint146`
- Row count: `7`
- Highest-alpha next gate: `MigrationInitiationThresholdForLargeData`
- Full Clay solved: `False`
- Clay promoted: `False`

## O/R/C/S/L/P/G/F

- O: Lane 6 owns only the Sprint 147 route-classifier script and generated outputs/ns_sprint147_blowup_route_classifier/ artifacts.
- R: Classify the post-Sprint146 route state exactly: WBF publishable, Gamma exact, symmetry-plane pure diffusion exact, migration exclusion failed, migration-driven structure identified, highest-alpha next gate selected, and Clay unpromoted.
- C: Single stdlib Python emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic staging directory.
- S: The state is not a Clay solution: exact local/control facts coexist with a failed global maximum-location exclusion and a live threshold gate.
- L: Use fixed route rows, validate required classifications and false promotion flags, then fail closed if any invariant is missing.
- P: Treat this as a deterministic route packet for Sprint 147 planning, not as a theorem prover or promotion mechanism.
- G: Validation passes only when all seven required route ids are present, the requested classifications match exactly, highest-alpha is unique, and all Clay solved/promoted flags remain false.
- F: Missing: MigrationInitiationThresholdForLargeData proof and the downstream global Clay Navier-Stokes promotion evidence.

## Route Classifications

| route_id | classification | status | alpha | action |
| --- | --- | --- | ---: | --- |
| wbf_tower | publishable | PUBLISHABLE_ROUTE_PACKET | 60 | publish_route_packet_without_promotion |
| gamma_max_principle | exact | EXACT_CONTROL_FACT | 90 | use_as_exact_constraint_for_all_route_rows |
| pure_diffusion_at_symmetry_plane | exact | EXACT_LOCAL_FACT | 80 | retain_as_local_support_not_global_barrier |
| maximum_location_migration_exclusion_for_v_barrier | failed | FAILED_GLOBAL_EXCLUSION | 100 | do_not_use_global_v_barrier_as_closed |
| migration_driven_blowup_structure | identified | IDENTIFIED_LIVE_STRUCTURE | 110 | route_future_work_through_migration_threshold_gate |
| migration_initiation_threshold_for_large_data | highest-alpha next gate | HIGHEST_ALPHA_NEXT_GATE | 120 | prioritize_as_highest_alpha_next_gate |
| full_clay_navier_stokes | not solved/promoted | NOT_SOLVED_NOT_PROMOTED | 0 | hold_no_clay_promotion |

## Fail-Closed Statement

This classifier publishes the route state only. It does not solve or promote the full Clay Navier-Stokes problem; the MigrationInitiationThresholdForLargeData gate remains open.
