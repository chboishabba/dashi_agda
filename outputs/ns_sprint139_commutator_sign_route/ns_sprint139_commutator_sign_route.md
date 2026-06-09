# NS Sprint 139 Commutator Sign Route

- Contract: `ns_sprint139_commutator_sign_route`
- Gate: `PointwiseSignDominanceRouteForRadialCommutator`
- Required theorem: `PointwiseRadialCommutatorSignOrDominanceForVBarrier`
- Route decision: `pointwise_sign_route_open_fail_closed`
- Commutator sign route closed: `false`
- Commutator domination closed: `false`
- Proof closed: `false`
- Clay Navier-Stokes promoted: `false`

## Barrier Equation

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Decision

The pointwise sign/dominance route is recorded but remains open. The required theorem is unavailable, the proof is not closed, and no Clay promotion is emitted.

## Rows

| Row | Status | Class | Local Condition | Commutator Effect |
| --- | --- | --- | --- | --- |
| `route_inventory` | `encoded_open_gate` | `equation_inventory` | At a first interior positive maximum of v=partial_z u1, v>0, partial_r v=partial_z v=0, and Ltilde v<=0. | The radial commutator is nonhomogeneous in v and can inject positive forcing at the crossing unless a pointwise sign or a quantitative dominance margin is supplied. |
| `sign_known_favorable_case` | `conditional_route_only` | `sign_known` | Assume sign(partial_z u^r) agrees with sign(partial_r u1) so that -(partial_z u^r) partial_r u1 <= 0 at the crossing. | Under this conditional sign, the radial commutator cannot create the first positive v crossing. |
| `sign_unknown_crossing_case` | `live_obstruction` | `sign_unknown` | No theorem fixes the correlation between partial_z u^r and partial_r u1 at an arbitrary first positive maximum of v. | The positive part max(-(partial_z u^r) partial_r u1, 0) remains an uncontrolled source in the pointwise barrier inequality. |
| `domination_hypothesis_pointwise_margin` | `hypothesis_required_not_proved` | `domination_hypothesis` | At every first positive maximum, max(-(partial_z u^r) partial_r u1, 0) <= M_point, where M_point is supplied by favorable concavity, diffusion, or source sign. | A strict pointwise margin would absorb positive commutator bursts before v crosses above zero. |
| `domination_hypothesis_weighted_barrier` | `hypothesis_required_not_proved` | `domination_hypothesis` | Use a weighted barrier B=w(r,z,t)v and require the positive commutator source to be absorbed by weight-generated drift, diffusion, and source margins. | A successful weight could trade pointwise sign for a quantitative dominance inequality over the crossing set. |
| `biot_savart_log_hazard` | `open_hazard` | `biot_savart_log_hazard` | partial_z u^r is recovered nonlocally from the axisymmetric Biot-Savart law and may inherit the coincident-ring logarithmic strain loss. | Even if partial_r u1 is locally bounded, a log-amplified partial_z u^r estimate can exceed a polynomial pointwise margin. |
| `radial_gradient_coupling` | `coupling_open` | `radial_gradient_coupling` | The factor partial_r u1 is not fixed by the axial condition v=partial_z u1 at the first positive maximum. | Radial steepening of u1 can amplify the commutator independently of the axial monotonicity variable v. |
| `fail_closed_required_theorem` | `fail_closed` | `required_theorem` | PointwiseRadialCommutatorSignOrDominanceForVBarrier must prove either favorable sign or quantitative dominance for -(partial_z u^r) partial_r u1 on every admissible first-crossing configuration. | Until that theorem is supplied, the pointwise sign route does not close the v-barrier. |

## Control Card

- O: Worker owns only scripts/ns_sprint139_commutator_sign_route.py and outputs/ns_sprint139_commutator_sign_route/.
- R: Record the pointwise sign/dominance route for -(partial_z u^r) partial_r u1 in the v-barrier.
- C: Emit deterministic JSON, CSV, and Markdown artifacts with fail-closed validation.
- S: Rows cover sign-known, sign-unknown, domination hypotheses, Biot-Savart log hazard, radial-gradient coupling, and the required theorem.
- L: The route inventory is complete, but the sign/dominance theorem is unavailable and the v-barrier is not closed.
- P: Use this as a Sprint 139 route ledger for future barrier work, not as a regularity proof.
- G: Validation succeeds only when proof closure, theorem availability, commutator domination, and Clay promotion all remain false.
- F: Missing required rows, closed sign-unknown case, hidden log-hazard closure, proof closure, or Clay promotion fails validation.
