# ns_sprint123_phase_locking_source_classifier

Deterministic Sprint123 classifier for NS phase-locking source status.

Recommended next lemma: FavorablePhaseLagWindowLowerBound
Recommended route id: nse_derived_rotating_frame_ode
Recommended classification: live_primary_requires_estimate
Primary route: nse_derived_rotating_frame_ode
Complete: false
Clay: false

Exit status: 1 because no complete Clay route exists.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| nse_derived_rotating_frame_ode | live_primary_requires_estimate | false | false | prove FavorablePhaseLagWindowLowerBound |
| imposed_phase_locking | rejected_circular | false | false | exclude from source accounting |
| sampled_dwell_windows | empirical_not_proof | false | false | use only as empirical guidance for the window estimate |
| damping_drift_balance | conditional_bound_missing | false | false | derive the missing bound after the primary estimate |
| global_data_realization | open_downstream | false | false | defer until the local phase-locking source is bounded |
| kstar_budget_bridge | open_downstream | false | false | defer until the phase-locking lower bound is available |
