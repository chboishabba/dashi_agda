# NS Sprint 129 Advective Concentration Audit

- Audit: `ns_sprint129_advective_concentration_audit`
- Verdict: `FAIL_CLOSED`
- Complete: `false`
- Exit code: `1`
- Clay Navier-Stokes promoted: `false`
- Primary open gate: `AdvectiveConcentrationVsDiffusionBound`
- Single remaining open question: `||u1||_inf >= c ||omega1||_inf`
- Passed rows: `8 / 9`

## PDE Facts

- `variables`: `{'u1': 'u^theta / r', 'omega1': 'omega^theta / r', 'psi1': 'psi^theta / r'}`
- `transport_velocity`: `{'u_r': '-r partial_z psi1', 'u_z': '2 psi1 + r partial_r psi1'}`
- `u1_equation`: `partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = nu (partial_r^2 + (3/r) partial_r + partial_z^2) u1`
- `omega1_equation`: `partial_t omega1 + u^r partial_r omega1 + u^z partial_z omega1 = nu (partial_r^2 + (3/r) partial_r + partial_z^2) omega1 + partial_z(u1^2)`
- `stream_equation`: `-(partial_r^2 + (3/r) partial_r + partial_z^2) psi1 = omega1`
- `u1_source`: `0`
- `pure_diffusion_u1`: `True`
- `omega1_source`: `partial_z(u1^2)`
- `omega1_source_term`: `partial_z(u1^2) = 2 u1 partial_z u1`
- `biot_savart_kernel`: `axisymmetric 5D Poisson kernel for psi1 with no logarithmic loss recorded`
- `no_log_axisymmetric_biot_savart`: `True`

## Rows

| Gate | Expected | Actual | Passed | Evidence |
| --- | --- | --- | --- | --- |
| `ExactAxisymmetricSwirlPDEFacts` | `u1/omega1/psi1 equations and velocity reconstruction encoded` | `encoded` | `True` | `{"biot_savart_kernel": "axisymmetric 5D Poisson kernel for psi1 with no logarithmic loss recorded", "no_log_axisymmetric_biot_savart": true, "omega1_equation": "partial_t omega1 + u^r partial_r omega1 + u^z partial_z omega1 = nu (partial_r^2 + (3/r) partial_r + partial_z^2) omega1 + partial_z(u1^2)", "omega1_source": "partial_z(u1^2)", "omega1_source_term": "partial_z(u1^2) = 2 u1 partial_z u1", "pure_diffusion_u1": true, "stream_equation": "-(partial_r^2 + (3/r) partial_r + partial_z^2) psi1 = omega1", "transport_velocity": {"u_r": "-r partial_z psi1", "u_z": "2 psi1 + r partial_r psi1"}, "u1_equation": "partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = nu (partial_r^2 + (3/r) partial_r + partial_z^2) u1", "u1_source": "0", "variables": {"omega1": "omega^theta / r", "psi1": "psi^theta / r", "u1": "u^theta / r"}}` |
| `PureDiffusionOfU1Claim` | `true for exact swirl PDE` | `true` | `True` | `u1 source term is 0` |
| `Omega1SourceTerm` | `partial_z(u1^2)` | `partial_z(u1^2)` | `True` | `partial_t omega1 + u^r partial_r omega1 + u^z partial_z omega1 = nu (partial_r^2 + (3/r) partial_r + partial_z^2) omega1 + partial_z(u1^2)` |
| `NoLogAxisymmetricBiotSavart` | `no logarithmic loss recorded` | `axisymmetric 5D Poisson kernel for psi1 with no logarithmic loss recorded` | `True` | `-(partial_r^2 + (3/r) partial_r + partial_z^2) psi1 = omega1` |
| `ViscousFeasibilityWindow` | `alpha in (1,3/2), beta=alpha-1 in (0,1/2)` | `alpha=4/3, beta=1/3` | `True` | `{"alpha": "4/3", "alpha_float": 1.3333333333333333, "alpha_window": "1 < alpha < 3/2", "alpha_window_passed": true, "beta": "1/3", "beta_float": 0.3333333333333333, "beta_relation": "beta = alpha - 1", "beta_relation_passed": true, "beta_window": "0 < beta < 1/2", "beta_window_passed": true, "passed": true}` |
| `SingleRemainingOpenQuestion` | `||u1||_inf >= c ||omega1||_inf` | `unresolved` | `True` | `the audit records exactly one open mathematical requirement` |
| `AdvectiveConcentrationVsDiffusionBound` | `closed proof of ||u1||_inf >= c ||omega1||_inf` | `open` | `False` | `no deterministic lower bound from omega1 concentration to u1 amplitude is encoded` |
| `ClayNavierStokesPromotion` | `false` | `false` | `True` | `Sprint 129 remains fail-closed while AdvectiveConcentrationVsDiffusionBound is open` |
| `forbidden marker scan` | `zero hits` | `0` | `True` | `[]` |

## Control Card

- O: Worker 1 owns only the Sprint129 advective concentration audit script and output directory
- R: record exact axisymmetric swirl PDE facts and isolate the advective concentration versus diffusion blocker
- C: deterministic Python audit emitting rows JSON, summary JSON, and Markdown
- S: all local PDE and parameter-window checks close; Clay promotion stays false
- L: the ledger has exactly one failing row, the lower-bound gate AdvectiveConcentrationVsDiffusionBound
- P: hold Navier-Stokes promotion until ||u1||_inf >= c ||omega1||_inf is proved in the required regime
- G: process exit code is 1 by design while the primary open gate is unresolved
- F: any added open gate, marker hit, window failure, or Clay promotion would violate the fail-closed audit
