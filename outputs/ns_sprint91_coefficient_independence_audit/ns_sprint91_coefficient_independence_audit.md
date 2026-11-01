# NS Sprint 91 Coefficient Independence Audit

- Contract: `ns_sprint91_coefficient_independence_audit`
- Decision: `FAIL_CLOSED`
- Route decision: `fail-closed`
- Candidate sources: `5`
- Accepted sources: `0`

## Rule

The route opens only if one allowed source avoids forbidden dependencies and supplies both pointwise H1 tail and an epsilon coefficient independent of target absorption.

## Candidate Sources

| Source | H1 tail | Independent coefficient | Forbidden hits | Classification | Decision |
| --- | --- | --- | --- | --- | --- |
| fixed-K LP identity | `False` | `False` | `none` | `IDENTITY_ONLY_NO_POINTWISE_OR_COEFFICIENT` | `fail-closed` |
| adjacent leakage bound | `False` | `False` | `target_absorption; epsilon_from_absorption` | `TARGET_ABSORPTION_COEFFICIENT_REUSE` | `fail-closed` |
| local-enstrophy candidate | `False` | `False` | `none` | `REDUCTION_BOOKKEEPING_ONLY` | `fail-closed` |
| scalar epsilon solver | `False` | `False` | `none` | `SOLVER_REQUIRES_EVIDENCE` | `fail-closed` |
| target absorption | `False` | `False` | `target_absorption; desired_conclusion; epsilon_from_absorption` | `FORBIDDEN_TARGET_SELF_USE` | `fail-closed` |

## Gates

- G1 AllowedSourceConsidered: `PASS`
- G2 AllowedPointwiseH1Tail: `FAIL_CLOSED`
- G3 AllowedIndependentCoefficient: `FAIL_CLOSED`
- G4 SameSourceEvidenceComplete: `FAIL_CLOSED`

## Open Obligations

- prove a pointwise-in-time danger-shell H1 tail without continuation/Serrin/BKM/theta/Clay inputs
- fix an epsilon coefficient before and independently of target absorption
- record both facts on one allowed source surface before promoting the absorption route
