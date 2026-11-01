# NS Sprint 140 Failure Mode Matrix

- Contract: `ns_sprint140_failure_mode_matrix`
- Sprint: `140` after Sprint `139`
- Parent route: `ConditionalRegularityAssembly`
- Route decision: `fail_closed_failure_modes_open`
- Failure modes open: `8`
- Conditional barrier assembly closed: `false`
- Global proof open: `true`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Rows hash: `668aa47750b9c63f6f295f1f5555a943afc78509974efe3b118ad99e6019846b`

## Failure Modes

| Failure | Category | Status | Trigger | Barrier Effect | Row Hash |
| --- | --- | --- | --- | --- | --- |
| `assumption_false_global_concavity_or_kernel_dominance` | `single_assumption_false` | `open_fail_closed` | The global concavity or kernel-dominance assumption is false. | The conditional v-barrier implication is unavailable even if the other two assumptions hold. | `b8f86af623b8bdecc095eef1922a4f00ca744080fffe688ac9bc2754d6f3e979` |
| `assumption_false_secondary_peak_exclusion` | `single_assumption_false` | `open_fail_closed` | The secondary-peak exclusion assumption is false. | Primary-region estimates do not rule out the first positive v crossing. | `fb866b0049b9fc22de341dd434398875ef41deb1c2cc8c4bf76bcf14cd9c54d8` |
| `assumption_false_transport_commutator_domination` | `single_assumption_false` | `open_fail_closed` | The transport-commutator domination assumption is false. | The maximum-principle inequality can be violated by an uncontrolled positive commutator burst. | `bc884aa20bd276bcab28801093afb4015c4aedb6adc4bbc5dacbed91ebf0d4a6` |
| `constants_incompatible_across_assumptions` | `interface_failure` | `open_fail_closed` | All three assumptions are stated, but their constants cannot be made simultaneous. | The conditional assembly fails at the interface between analytic gates. | `b5e767541f85111b9693eca9d960c7d8371386a7a1955aff8e5826cdef14b7fb` |
| `off_center_first_positive_crossing` | `crossing_geometry` | `open_fail_closed` | The first positive v crossing occurs off-center or outside the monitored core. | A monitored-route barrier cannot exclude unmonitored off-center first crossings. | `ec9e2d445335f00bb4f443343aa5998ddd9e1adc1ef53214e81aa0329883d254` |
| `boundary_or_annular_kernel_sign` | `kernel_sign_failure` | `open_fail_closed` | Boundary-sensitive or annular kernel contributions have the wrong sign. | The concavity input cannot be promoted from local support to global barrier closure. | `5328c747500a215815d4e4e97f98569b43b8c7ba9b1ad0687ab9682a2713966c` |
| `commutator_biot_savart_log_loss` | `commutator_budget_failure` | `open_fail_closed` | The commutator estimate carries an unabsorbed Biot-Savart logarithmic loss. | Transport-commutator domination remains open until the log loss is absorbed, canceled, or avoided. | `8839e2edccafede9de58f09c452c43e3bc24064600e82e5601da92b01ad063c9` |
| `monitored_route_to_full_clay_translation_absent` | `promotion_boundary` | `open_fail_closed` | The monitored conditional route is not translated to the full Clay class. | No global Clay Navier-Stokes theorem or promotion can be emitted from the conditional assembly. | `7a5aeb76fc69042155312fc63373a322f1c42d9edf58d32447986325e6d2d8b3` |

## Source Summary Hashes

- route_fork_classifier: `9bdb653546f25be25edc99c7e56c6e30b10259241cde594218a5925764828e14`
- kernel_sign_sampler: `5b277b26f0e237011ce2106ccdaaa3ea9b76eed7f1f26b3af0c11a857cf0da45`
- commutator_sign_route: `73c1eae285b50c095877ed41128083bb99eb7726b3c733415f212b6431f9b78c`

## Guard

This matrix records why the conditional barrier assembly must remain fail-closed. Any single failed assumption, incompatible constants, unresolved crossing geometry, kernel sign defect, commutator log loss, or absent full-class translation keeps the route open and blocks Clay promotion.

## Control Card

- O: Worker 4 owns only scripts/ns_sprint140_failure_mode_matrix.py and outputs/ns_sprint140_failure_mode_matrix/.
- R: Inventory conditional-barrier failure modes: any one of the three assumptions false, incompatible constants, off-center crossing, boundary/annular kernel sign, commutator log loss, and absent monitored-route to full Clay translation.
- C: Deterministic stdlib Python emitter with dataclass rows, stable SHA-256 hashes, JSON, CSV, Markdown, and fail-closed validation.
- S: All requested failure modes are present and open; the conditional assembly, global proof, and Clay promotion remain closed only in the negative sense: no proof is emitted.
- L: Sprint 139 route inventory -> Sprint 140 failure matrix -> open blocker rows -> no monitored-route closure -> no Clay promotion.
- P: Use the matrix as a guardrail for conditional assembly work, not as a regularity theorem.
- G: Validation succeeds only if route_decision is fail_closed_failure_modes_open, every failure row is open, and proof/promotion flags remain false.
- F: Missing required failure rows, route-decision mismatch, monitored-route closure, global proof claim, full Clay NS claim, or Clay promotion fails validation.
