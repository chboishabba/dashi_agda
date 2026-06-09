# NS Sprint 132 Partial Obstruction Theorem

- Contract: `ns_sprint132_partial_obstruction_theorem`
- Theorem: `NSPartialRegularityFromObstructionTower`
- Class scope: `CLASS_WBF, CLASS_AXS`
- Route-specific obstruction: `true`
- Global regularity claim: `false`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Complete: `true`
- Exit code: `0`

## Theorem Statement

No mechanism in CLASS_WBF union CLASS_AXS can produce finite-time BKM blowup within the analyzed route classes; this is route-specific and is not a global Clay Navier-Stokes regularity claim.

## Rows

| Route | Class | Mechanism | Status | Condition | Formula | Obstructed |
| --- | --- | --- | --- | --- | --- | --- |
| `WBF-L` | `CLASS_WBF` | passive linear strain sign | `exact` | `-` | `sign(Pi^{HH->L}) = -sign(gamma)` | `true` |
| `WBF-S` | `CLASS_WBF` | self-generated strain | `exact` | `-` | `n dot S_self dot n = 2/3` | `true` |
| `WBF-MP` | `CLASS_WBF` | multi-packet Reynolds stress | `exact` | `-` | `||Gram||_F^2 >= N^2/3` | `true` |
| `WBF-R` | `CLASS_WBF` | rotating background strain | `exact` | `-` | `integral zero` | `true` |
| `WBF-V` | `CLASS_WBF` | vortex stretching H^s data | `conditional_on` | `omega in H1` | `gamma <= C Omega log Omega + CF93 conflict` | `true` |
| `AXS` | `CLASS_AXS` | axisymmetric Hou-Luo beta>0 | `conditional_on` | `NoLogAxisymmetricBiotSavartUniform` | `nu/(T*-t)^(3 beta)->infty` | `true` |

## Conditional Requirements

- `WBF-V`: `omega in H1`
- `AXS`: `NoLogAxisymmetricBiotSavartUniform`

## Control Card

- O: Worker 1 owns only the Sprint132 partial obstruction theorem script and generated output directory.
- R: Emit six route rows for WBF-L, WBF-S, WBF-MP, WBF-R, WBF-V, and AXS.
- C: Deterministic Python emitter writes rows JSON, summary JSON, and Markdown report.
- S: Four WBF rows are exact; WBF-V and AXS are conditional on their stated hypotheses.
- L: The obstruction tower ranges only over analyzed CLASS_WBF union CLASS_AXS route classes.
- P: Conclude NSPartialRegularityFromObstructionTower as a route-specific obstruction theorem.
- G: No row produces a finite-time BKM blowup mechanism within the analyzed routes.
- F: Full Clay Navier-Stokes regularity remains false and unpromoted.
