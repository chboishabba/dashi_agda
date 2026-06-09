# ns_sprint122_persistence_source_classifier

Deterministic Sprint122 classifier for NS persistence-source route status.

Recommended next lemma: RotatingFramePhaseLockingEstimate
Recommended route id: rotating_frame_ode
Recommended classification: conditional_model_not_bound
Primary route: rotating_frame_ode
Complete: false
Clay: false

Exit status: 1 because no Clay route closes.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| rotating_frame_ode | conditional_model_not_bound | false | false | prove RotatingFramePhaseLockingEstimate |
| imposed_phase_lag | rejected_circular | false | false | exclude from route accounting |
| numerical_phase_locking | empirical_not_proof | false | false | use only as empirical guidance |
| nonlinear_feedback | open_secondary | false | false | keep as a secondary route after the primary estimate |
| global_data_realization | open_downstream | false | false | defer until the conditional route is bounded |
