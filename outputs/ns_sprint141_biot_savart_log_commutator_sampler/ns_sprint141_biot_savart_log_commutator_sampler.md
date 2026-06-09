# Sprint 141 Biot-Savart Log Commutator Sampler

## Decision

Local bounded rows coexist with near-coincident ring/off-axis annulus log-loss hazard rows; log-aware commutator domination is not proved.

- Route decision: `fail_closed_log_loss_hazard_open`
- Log-aware commutator domination proved: `false`
- Global Navier-Stokes proof claimed: `false`
- Clay promotion allowed: `false`

## Ledger

| row | case | geometry | sep | log amp | comm proxy | ratio | local | hazard | class |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | local_ring_separated_moderate | coaxial_ring_pair | 0.281602556807 | 1.51536986751 | 0.145652055227 | 0.202294521148 | true | false | local_bounded_log_row |
| r001 | off_axis_annulus_local | off_axis_annulus | 0.240831891576 | 1.6394381692 | 0.0933646143815 | 0.135311035335 | true | false | local_bounded_log_row |
| r002 | near_coincident_ring_log_loss | nearly_coincident_coaxial_rings | 0.00412310562562 | 5.49526323587 | 0.869580116446 | 1.17510826547 | false | true | log_loss_hazard_commutator_domination_unproved |
| r003 | off_axis_annulus_grazing_log_loss | grazing_off_axis_annuli | 0.015 | 4.21459369037 | 0.666338923379 | 0.876761741288 | false | true | log_loss_hazard_commutator_domination_unproved |
| r004 | multi_scale_annulus_unresolved | nested_off_axis_annuli | 0.00335410196625 | 5.70091970417 | 0.88895697082 | 1.26993852974 | false | true | log_loss_hazard_commutator_domination_unproved |

## Validation

The artifact contains both local bounded rows and log-loss hazard rows. Every row and the summary keep global proof, route closure, and promotion flags false.
