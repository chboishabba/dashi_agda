# NS Sprint 93 Candidate-Source Matrix Audit

- Contract: `ns_sprint93_candidate_source_matrix_audit`
- Decision: `FAIL_CLOSED`
- Route decision: `fail-closed`
- Candidate sources: `15`
- Accepted sources: `0`

## Fail-Closed Rule

A candidate is accepted only when one allowed source supplies dominance, pointwise H1 tail, and an independent coefficient, and avoids target absorption, BKM, Serrin, H1 continuation, theta preservation, desired conclusion, and epsilon-from-absorption dependencies.

## Matrix

| Source | Dominance | H1 tail | Independent coefficient | Avoids forbidden | Same-source complete | Classification | Decision |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Sprint87 absorption scaling | `False` | `False` | `False` | `True` | `False` | `SCALAR_CONDITION_ONLY` | `fail-closed` |
| Sprint87 danger-shell factorization | `False` | `False` | `False` | `True` | `False` | `FACTORIZATION_SUPPORT_ONLY` | `fail-closed` |
| Sprint88 H1 tail decision | `False` | `False` | `False` | `True` | `False` | `TAIL_GATE_RECORDED_OPEN` | `fail-closed` |
| Sprint88 tail source classifier | `False` | `False` | `False` | `True` | `False` | `ALL_TAIL_CANDIDATES_FAIL_CLOSED` | `fail-closed` |
| Sprint89 circularity matrix | `False` | `False` | `False` | `True` | `False` | `NO_ALLOWED_ROUTE` | `fail-closed` |
| Sprint89 pointwise H1 mechanism | `False` | `False` | `False` | `True` | `False` | `MECHANISM_OPEN` | `fail-closed` |
| Sprint90 epsilon budget solver | `False` | `False` | `False` | `True` | `False` | `SOLVER_NEEDS_SUPPLIED_EVIDENCE` | `fail-closed` |
| Sprint90 local enstrophy | `False` | `False` | `False` | `True` | `False` | `LOCAL_ENSTROPHY_REDUCTION_ONLY` | `fail-closed` |
| Sprint91 coefficient independence | `False` | `False` | `False` | `True` | `False` | `NO_INDEPENDENT_COEFFICIENT_SOURCE` | `fail-closed` |
| Sprint91 localized flux identity | `False` | `False` | `False` | `True` | `False` | `IDENTITY_BOOKKEEPING_ONLY` | `fail-closed` |
| Sprint92 high-high dominance budget | `False` | `False` | `False` | `True` | `False` | `DOMINANCE_BUDGET_FAIL_CLOSED` | `fail-closed` |
| Sprint92 moving K* boundary | `False` | `False` | `False` | `True` | `False` | `MOVING_BOUNDARY_OPEN` | `fail-closed` |
| Split-source dominance tail coefficient attempt | `False` | `False` | `False` | `True` | `False` | `REJECT_SPLIT_SOURCE_ASSEMBLY` | `fail-closed` |
| Adjacent leakage / target absorption reuse | `False` | `False` | `False` | `False` | `False` | `REJECT_TARGET_ABSORPTION_EPSILON_REUSE` | `fail-closed` |
| Target conclusion / continuation shortcuts | `True` | `True` | `True` | `False` | `True` | `REJECT_FORBIDDEN_DEPENDENCIES_EVEN_IF_COMPLETE` | `fail-closed` |

## Rejections

- `Adjacent leakage / target absorption reuse` rejected for `target_absorption; epsilon_from_absorption`.
- `Target conclusion / continuation shortcuts` rejected for `target_absorption; bkm; serrin; h1_continuation; theta_preservation; desired_conclusion; epsilon_from_absorption`.

## Open Obligations

- supply dominance before using target absorption
- supply pointwise H1 tail without BKM/Serrin/H1 continuation/theta preservation
- supply an independent coefficient not derived from absorption
- record dominance, tail, and coefficient on the same allowed source
