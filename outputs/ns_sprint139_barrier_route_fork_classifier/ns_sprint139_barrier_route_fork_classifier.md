# NS Sprint 139 Barrier Route Fork Classifier

- Contract: `ns_sprint139_barrier_route_fork_classifier`
- Sprint: `139` after Sprint `138`
- Parent gate: `AxialMonotonicityOfSwirlProfile`
- Decision: `fail_closed_ranked_forks`
- Recommended next route: `ConditionalRegularityAssembly`
- Second priority route: `TransportCommutatorDomination`
- Global proof open: `true`
- Global barrier closed: `false`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Rows hash: `6bc117e0614d9965093ec4f037515c397c1a266da925d8006a62ee97935fde3b`

## Ranked Routes

| Rank | Route | Classification | Status | Action | Fallback Trigger | Row Hash |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `ConditionalRegularityAssembly` | `conditional_assembly_not_global_proof` | `conditional_best_next_artifact` | rank_first_for_next_deterministic_artifact | Do not use as fallback; use this only to make dependencies and constants explicit while keeping the theorem conditional. | `e241150e11c7de11eead0f7d1572327591b95ab931ce22410edd1a8c7dc9be2d` |
| 2 | `TransportCommutatorDomination` | `open_budget_domination_route` | `open_high_priority` | prioritize_as_next_analytic_fork | Select fallback if log-aware commutator domination cannot be absorbed by any local concavity or weighted barrier margin. | `781e4eb1d0a3e8194223acf09b1b5c6aa26b7b28acd89937cd98bdffad033f9f` |
| 3 | `GlobalConcavityOfPsi1` | `open_primary_blocker` | `open_not_promotable` | keep_open_but_do_not_promote | Select fallback if global sign/dominance is refuted or cannot be made boundary- and annulus-compatible. | `24327fb7255d7f00f7c61783fb1c0a63b5164aa2d5090ade80d894d9595f74b2` |
| 4 | `SecondaryPeakExclusion` | `open_shape_persistence_blocker` | `open_not_promotable` | keep_open_after_higher_priority_routes | Select fallback if a secondary crossing scenario survives all reasonable localization or zero-count replacements. | `fd3cfc8be1486f124a09ea1fe20ec174022f3aa3dcfeb7eea00b170787fdc0ac` |
| 5 | `RouteAbandonFallback` | `abandon_or_fallback_if_blockers_harden` | `fallback_available_not_selected_first` | hold_as_route_abandon_decision_point | Trigger when one of the three analytic gates is proved false or becomes structurally incompatible with the others. | `0d70c2c20073f4166d5de81afe709ee4bf7f5753b3276360013989f59d8c296c` |

## Source Summary Hashes

- global_concavity: `53c1ce698f08ddb7616562232587624de1fb1b6c5241439bb504c23a3067f230`
- secondary_peak: `6768c7bf5223a5099336116bfa3e77119cd63962731421e3419b730c00eba1b9`
- transport_commutator: `de558ab39204768885c8a4ce06835a8ead544d0b06395dce397d3075b1bb957c`

## Guard

This artifact ranks route work only. It keeps the global proof open, treats conditional regularity assembly as conditional, and emits no full Clay Navier-Stokes solution or promotion.

## Control Card

- O: Worker 2 owns only scripts/ns_sprint139_barrier_route_fork_classifier.py and outputs/ns_sprint139_barrier_route_fork_classifier/.
- R: Rank/fork the post-Sprint 138 routes: GlobalConcavityOfPsi1, SecondaryPeakExclusion, TransportCommutatorDomination, conditional regularity assembly, and route-abandon/fallback.
- C: Deterministic stdlib Python emitter with dataclass rows, stable SHA-256 hashes, validation, JSON, CSV, and Markdown.
- S: Conditional assembly is ranked first as the next artifact, transport commutator domination second as the next analytic fork, all global proof and Clay promotion flags remain false.
- L: Sprint 138 blockers -> ranked route forks -> conditional assembly surface -> fallback if blockers harden or conflict.
- P: Use this classifier to guide Sprint 139 route selection while explicitly keeping the global proof open.
- G: Validation passes only if every row keeps global_proof_open true and full Clay/Clay promotion/promotion_allowed false.
- F: Missing route rows, accidental global closure, full Clay NS claim, Clay promotion, or missing fallback fails validation.
