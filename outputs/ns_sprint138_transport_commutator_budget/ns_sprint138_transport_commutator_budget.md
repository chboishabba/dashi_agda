# NS Sprint 138 Transport Commutator Budget

- Contract: `ns_sprint138_transport_commutator_budget`
- Gate: `TransportCommutatorDominationForVBarrier`
- Commutator decision: `commutator_domination_open`
- Route decision: `fail_closed_no_global_barrier`
- Commutator domination closed: `false`
- Local barrier globally closed: `false`
- Clay Navier-Stokes promoted: `false`

## Barrier Equation

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Decision

Commutator domination is open; the local barrier is not globally closed; there is no Clay promotion.

## Rows

| Row | Status | Class | Term or Relation | Budget Effect |
| --- | --- | --- | --- | --- |
| `barrier_equation_inventory` | `encoded` | `equation_inventory` | D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v | Diffusion is nonpositive; homogeneous v terms are linear in the positive maximum; two nonhomogeneous terms remain: 2 u1 partial_z^2 psi1 and -(partial_z u^r) partial_r u1. |
| `homogeneous_v_terms_first_positive_max` | `linear_growth_not_obstruction_by_itself` | `homogeneous_v` | 2 v partial_z psi1 - (partial_z u^z) v | They can be placed in a Gronwall coefficient if the coefficient partial_z psi1 and partial_z u^z is time integrable along the barrier window. |
| `nonhomogeneous_radial_commutator` | `open_hazard` | `nonhomogeneous_commutator` | -(partial_z u^r) partial_r u1 | A local v barrier needs either a sign rule for -(partial_z u^r) partial_r u1 or a domination inequality against the favorable concavity/source/diffusion margin. |
| `incompressibility_relation_limitations` | `insufficient_for_domination` | `constraint_limitation` | partial_r u^r + u^r/r + partial_z u^z = 0; partial_z^2 u^z = -partial_z partial_r u^r - partial_z(u^r/r) | The homogeneous -(partial_z u^z)v can be rewritten as part of a trace-free strain coefficient, but the radial commutator remains a separate nonhomogeneous source. |
| `log_biot_savart_strain_hazard` | `open_log_loss` | `strain_hazard` | partial_z u^r, partial_z u^z, and partial_z psi1 inherit nonlocal Biot-Savart strain bounds with the restored coincident-ring logarithmic loss. | A polynomial viscous or local concavity margin is not enough unless it explicitly absorbs log-amplified strain. |
| `domination_hypothesis_pointwise_sign` | `hypothesis_not_established` | `possible_domination_hypothesis` | -(partial_z u^r) partial_r u1 <= 0 at every possible first positive maximum of v | This would reduce the local barrier back to homogeneous strain plus the already tracked 2 u1 partial_z^2 psi1 term. |
| `domination_hypothesis_integrated_margin` | `hypothesis_not_established` | `possible_domination_hypothesis` | \|(partial_z u^r) partial_r u1\| <= margin from -2 u1 partial_z^2 psi1, -nu Ltilde v, or an integrated barrier weight | The required estimate must be log-aware, boundary-aware, and valid at any first-crossing location, not only near the primary axial maximum. |
| `current_fail_closed_status` | `fail_closed` | `decision` | commutator domination open; local barrier not globally closed; no Clay promotion | Transport commutator domination remains an explicit open gate for any future Hou-Luo barrier proof. |

## Control Card

- O: Create only the Sprint138 transport commutator emitter and its output directory surface.
- R: Analyze the v=partial_z u1 barrier equation after Sprint137 with transport commutator terms made explicit.
- C: Emit deterministic JSON, CSV, and Markdown artifacts with validate() and main().
- S: Rows encode homogeneous v terms, the nonhomogeneous radial commutator, incompressibility limits, log strain hazard, possible domination hypotheses, and fail-closed status.
- L: The local first-positive-maximum ledger is recorded, but commutator domination is open and the local barrier is not globally closed.
- P: Use the artifact as a gate inventory for future Hou-Luo barrier work, not as a regularity proof.
- G: Validation succeeds only when commutator domination, global barrier closure, and Clay promotion all remain false.
- F: Missing required rows, missing commutator terms, accidental domination closure, global proof closure, or Clay promotion fails validation.
