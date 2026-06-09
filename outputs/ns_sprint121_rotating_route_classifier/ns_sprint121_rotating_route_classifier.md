# ns_sprint121_rotating_route_classifier

Deterministic Sprint121 classifier for NS rotating-route status.

Recommended next lemma: NonCircularRotatingStrainPersistenceBound
Recommended route id: rotating_strain_phase_lag
Recommended classification: conditional_open_requires_persistence
Primary route: rotating_strain_phase_lag
Complete: false
Clay: false

Exit status: 1 because no complete Clay route exists.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| rotating_strain_phase_lag | conditional_open_requires_persistence | false | false | prove NonCircularRotatingStrainPersistenceBound |
| constant_linear_strain | obstructed_by_sprint120 | false | false | retain as a Sprint120 obstruction record |
| nonlinear_feedback | open_secondary | false | false | keep as a secondary mechanism after the persistence gate |
| imposed_phase_lag | rejected_circular | false | false | exclude from non-circular route accounting |
| numerical_rotation_evidence | empirical_not_proof | false | false | use only as empirical guidance, not as a lemma substitute |
