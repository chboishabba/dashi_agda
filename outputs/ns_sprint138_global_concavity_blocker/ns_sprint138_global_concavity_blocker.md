# NS Sprint 138 Global Concavity Blocker

- Contract: `ns_sprint138_global_concavity_blocker`
- Blocker: `GlobalConcavityOfPsi1`
- Parent gate: `AxialMonotonicityOfSwirlProfile`
- Decision: `fail_closed_blocker_open`
- Local concavity supported: `true`
- Global concavity closed: `false`
- Blocker open: `true`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`

## Required Theorem

For every possible first positive maximum of v=partial_z u1 in the monitored half-profile, partial_z^2 psi1 must keep the sign needed to make 2 u1 partial_z^2 psi1 nonpositive or otherwise dominated.

## Rows

| Row | Status | Role | Statement | Obstruction |
| --- | --- | --- | --- | --- |
| `local_taylor_concavity_near_symmetry_center` | `supported_local` | `local_center_expansion` | At the z-reflection symmetry center, a local Taylor expansion can support partial_z^2 psi1<=0 in a small neighborhood of the primary axial maximum, provided the center is a genuine concave stream-profile peak. | This controls only a local patch and does not rule out off-center first positive crossings of v. |
| `elliptic_nonlocal_psi1_dependence_on_omega1` | `open_blocker` | `elliptic_nonlocality` | The stream variable psi1 is determined by the elliptic relation -Ltilde psi1 = omega1, so partial_z^2 psi1 depends nonlocally on the full omega1 distribution rather than only on the local sign structure near the symmetry center. | A local peak calculation for omega1 or psi1 cannot by itself force global concavity of psi1. |
| `sign_indefinite_kernel_contribution` | `open_blocker` | `kernel_sign` | The differentiated elliptic kernel contributing to partial_z^2 psi1 is sign-indefinite across source locations, so favorable near-center mass can be offset by remote or asymmetric omega1 contributions. | The maximum-principle source term 2 u1 partial_z^2 psi1 can become positive at an admissible crossing if the nonlocal kernel contribution has the wrong sign. |
| `boundary_annular_contribution` | `open_blocker` | `boundary_and_annulus` | Boundary layers, annular mass away from the axis, and outer domain contributions can alter partial_z^2 psi1 at an interior point even when the symmetry-center profile remains locally concave. | A first positive maximum of v can occur in an annular or near-boundary region where the local center concavity ledger has no sign authority. |
| `persistence_failure` | `open_blocker` | `time_persistence` | Even if the initial profile has a favorable concavity patch, the current route has no persistence theorem showing that partial_z^2 psi1 keeps the required sign over the time window needed for axial monotonicity. | The barrier argument needs sign control at the first crossing time, not merely at initial time or at the symmetry center. |
| `required_theorem_global_concavity_of_psi1` | `required_theorem_missing` | `closure_requirement` | For every possible first positive maximum of v=partial_z u1 in the monitored half-profile, partial_z^2 psi1 must keep the sign needed to make 2 u1 partial_z^2 psi1 nonpositive or otherwise dominated. | Without this theorem, AxialMonotonicityOfSwirlProfile cannot be closed from the local symmetry-center calculation. |

## Control Card

- O: Worker owns only scripts/ns_sprint138_global_concavity_blocker.py and outputs/ns_sprint138_global_concavity_blocker/.
- R: Analyze GlobalConcavityOfPsi1 as the first Sprint 138 blocker for AxialMonotonicityOfSwirlProfile.
- C: Deterministic stdlib Python emitter with dataclass rows, JSON, CSV, Markdown, validate(), and main().
- S: Local Taylor concavity near the symmetry center is supported; elliptic nonlocality, sign-indefinite kernels, boundary/annular terms, and persistence keep the global theorem open.
- L: local center expansion -> nonlocal psi1 dependence -> sign-indefinite kernel and boundary annulus -> persistence failure -> missing required theorem
- P: Keep the Sprint 138 route fail-closed until a global concavity theorem for psi1 is proved.
- G: Validation passes only if local concavity is recorded, global concavity remains unclosed, the blocker remains open, and Clay flags stay false.
- F: Missing required rows, closing global concavity, claiming axial monotonicity, flipping the full Clay NS guard, or promoting Clay fails validation.
