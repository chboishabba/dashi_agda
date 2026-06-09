# ns_sprint119_persistence_source_classifier

Deterministic Sprint119 classifier for Navier-Stokes persistence sources.

Recommended next lemma: PersistentAlignmentExistenceLowerBound
Recommended mechanism id: persistent_alignment_existence
Primary gate: persistent_alignment_existence
Non-circular source established: false
Complete: false
Clay: false

Exit status: 1 because no non-circular persistence source is established.

| mechanism_id | classification | non_circular_source | complete | clay | next_action |
| --- | --- | --- | --- | --- | --- |
| persistent_alignment_existence | open_primary_gate | false | false | false | prove PersistentAlignmentExistenceLowerBound |
| hyperbolic_strain_template | open_requires_construction | false | false | false | construct an admissible template and persistence estimate |
| beltrami_wave_packet_alignment | open_secondary | false | false | false | keep as a secondary comparison mechanism |
| local_smooth_continuation | short_time_conditional_not_global_source | false | false | false | use only for conditional short-time propagation |
| leray_energy_bounds | magnitude_only_no_alignment_duration | false | false | false | retain as magnitude bookkeeping |
| numerical_vortex_alignment | empirical_not_proof | false | false | false | treat as heuristic evidence only |
| imposed_alignment_assumption | rejected_circular | false | false | false | exclude from source accounting |
