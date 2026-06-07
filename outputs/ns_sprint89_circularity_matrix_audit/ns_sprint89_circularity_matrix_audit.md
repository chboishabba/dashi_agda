# NS Sprint 89 Circularity Matrix Audit

- Contract: `ns_sprint89_circularity_matrix_audit`
- Route decision: `fail-closed`
- Allowed routes: `0`
- Candidate routes: `5`

## Rule

route opens only when a candidate avoids H1 continuation, Serrin, BKM, target absorption, theta preservation, Clay regularity, and desired conclusion dependencies while supplying both pointwise H1 tail and an independent epsilon coefficient

## Matrix

| Route | Candidate input | H1 tail | Independent epsilon | Forbidden hits | Classification | Decision |
| --- | --- | --- | --- | --- | --- | --- |
| `R1` | Leray energy | `False` | `False` | `none` | `INSUFFICIENT_ENERGY_LEVEL_ONLY` | `fail-closed` |
| `R2` | KStar admissibility | `False` | `False` | `none` | `INSUFFICIENT_SCALE_SELECTION_ONLY` | `fail-closed` |
| `R3` | Time-integrated dissipation | `False` | `False` | `none` | `INSUFFICIENT_TIME_INTEGRATED` | `fail-closed` |
| `R4` | Danger-shell local mechanism | `False` | `False` | `target_absorption; desired_conclusion` | `FORBIDDEN_TARGET_REUSE` | `fail-closed` |
| `R5` | Critical coefficient smallness | `False` | `False` | `target_absorption` | `INSUFFICIENT_COEFFICIENT_ONLY` | `fail-closed` |

## Next Required Inputs

- supply a pointwise H1 tail theorem independent of continuation/Serrin/BKM/theta/Clay regularity
- supply an epsilon absorption coefficient not derived from target absorption
- verify both inputs occur on the same allowed route before opening the NS pointwise H1 tail gate
