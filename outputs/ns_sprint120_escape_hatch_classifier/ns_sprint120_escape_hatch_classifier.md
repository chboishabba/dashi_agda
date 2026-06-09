# ns_sprint120_escape_hatch_classifier

Deterministic Sprint120 classifier for post-anti-correlation NS route status.

Recommended next lemma: RotatingStrainDecorrelationMechanism
Recommended route id: rotating_strain
Recommended classification: remaining_open_requires_new_mechanism
Primary open route: rotating_strain
Complete: false
Clay: false

Exit status: 1 because no complete Clay route exists.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| constant_linear_strain_route | obstructed_closed | false | false | retain only as a closed obstruction record |
| rotating_strain | remaining_open_requires_new_mechanism | false | false | prove RotatingStrainDecorrelationMechanism |
| nonlinear_feedback | self_interacting_packet_open | false | false | analyze self-interacting packet closure without imposed flux |
| vorticity_coupling | open_secondary | false | false | keep as a secondary coupling route |
| imposed_positive_flux | rejected_circular | false | false | exclude from post-anti-correlation route accounting |
