# NS Sprint 132 Gap Inventory Classifier

- Contract: `ns_sprint132_gap_inventory_classifier`
- Row count: `11`
- Closed exact count: `4`
- Conditionally closed count: `2`
- Open count: `5`
- Single load-bearing missing lemma: `NoLogAxisymmetricBiotSavartUniform`
- Recommended next action: `attempt_NoLogAxisymmetricBiotSavartUniform`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Complete: `true`
- Exit code: `0`

## Publishable Now

- `WBF no-go tower`
- `axisymmetric moderate-Re regularization`

## Inventory Rows

| gap_name | classification | programme_area | load_bearing_for_full_clay | missing_lemma | next_action |
| --- | --- | --- | --- | --- | --- |
| anti-correlation | closed_exact | WBF no-go tower | false | - | package_WBF_no_go_tower |
| Gram matrix | closed_exact | WBF no-go tower | false | - | package_WBF_no_go_tower |
| multi-packet Reynolds stress | closed_exact | WBF no-go tower | false | - | package_WBF_no_go_tower |
| zero-mean rotation cycle | closed_exact | WBF no-go tower | false | - | package_WBF_no_go_tower |
| vortex-stretching log-gap obstruction | conditionally_closed | axisymmetric regularization | true | NoLogAxisymmetricBiotSavartUniform | attempt_NoLogAxisymmetricBiotSavartUniform |
| Hou-Luo viscous obstruction beta>0 | conditionally_closed | axisymmetric moderate-Re regularization | true | NoLogAxisymmetricBiotSavartUniform | attempt_NoLogAxisymmetricBiotSavartUniform |
| large-Re axisymmetric | open | full Clay Navier-Stokes gap map | true | NoLogAxisymmetricBiotSavartUniform | attempt_NoLogAxisymmetricBiotSavartUniform |
| marginal beta=0 | open | full Clay Navier-Stokes gap map | false | - | retain_as_open_gap |
| Euler nu=0 | open | full Clay Navier-Stokes gap map | false | - | retain_as_open_gap |
| non-resonant triads | open | full Clay Navier-Stokes gap map | false | - | retain_as_open_gap |
| multi-scale concentration | open | full Clay Navier-Stokes gap map | false | - | retain_as_open_gap |

## Control Card

- O: Worker 3 owns only the Sprint132 gap inventory classifier script and output directory
- R: encode the complete NS programme gap map with exact, conditional, and open classifications
- C: deterministic Python emitter writes rows JSON, summary JSON, and Markdown report
- S: four WBF obstructions are closed_exact, two axisymmetric obstructions are conditionally_closed, and five regimes remain open
- L: the only load-bearing missing lemma surfaced for the next move is NoLogAxisymmetricBiotSavartUniform
- P: publish WBF no-go tower and axisymmetric moderate-Re regularization without Clay promotion
- G: exit code is 0 exactly when the inventory is complete and Clay flags remain false
- F: any claim of full Clay Navier-Stokes promotion is outside this classifier
