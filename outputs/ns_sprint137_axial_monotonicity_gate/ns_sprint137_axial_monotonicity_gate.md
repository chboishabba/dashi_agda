# NS Sprint 137 Axial Monotonicity Gate

- Contract: `ns_sprint137_axial_monotonicity_gate`
- Gate: `AxialMonotonicityOfSwirlProfile`
- Route decision: `conditional_fail_closed`
- Local barrier supported: `true`
- Global proof closed: `false`
- Open blockers: `global_concavity_blocker, secondary_peak_blocker`
- Clay Navier-Stokes promoted: `false`

## Barrier Equation

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Rows

| Row | Status | Role | Statement | Effect |
| --- | --- | --- | --- | --- |
| `symmetry_inheritance` | `supported_local` | `symmetry` | If u1 is even about the axial symmetry plane z=0, then v=partial_z u1 is odd and v=0 on the symmetry plane. | The monitored half-profile can impose a zero barrier at the symmetry plane before searching for a first positive crossing. |
| `v_initial_sign` | `assumption_tracked` | `initial_barrier` | The candidate monotone half-profile starts with v<=0 on the chosen side of the symmetry plane, with compatible boundary and decay conditions. | A sign-preservation proof may begin only after this initial barrier is explicitly part of the data class. |
| `first_positive_crossing_criterion` | `supported_local` | `first_crossing` | At the first time when v becomes positive in the monitored half-profile, the interior positive maximum has v>0, partial_r v=partial_z v=0, and Ltilde v<=0. | At a first positive interior maximum, the transport drift is harmless and the parabolic contradiction reduces to the sign of source and commutator terms. |
| `source_derivative_term` | `conditional` | `differentiated_source` | Differentiating the corrected u1 equation gives the source ledger term 2 v partial_z psi1 + 2 u1 partial_z^2 psi1, plus transport commutators. | The dangerous nonhomogeneous term at a first positive maximum is 2 u1 partial_z^2 psi1; it must be nonpositive or dominated to close the barrier. |
| `local_concavity_support` | `supported_local` | `local_barrier_closure` | Near the symmetric axial maximum, local concavity of the stream profile supports partial_z^2 psi1<=0 in the active barrier region when u1>=0. | On this local patch, 2 u1 partial_z^2 psi1 is nonpositive, so the first-crossing contradiction is locally plausible. |
| `diffusion_at_positive_max_sign` | `supported_local` | `diffusion_sign` | At an interior positive maximum of v away from r=0, Ltilde v = partial_r^2 v + (3/r)partial_r v + partial_z^2 v is nonpositive because partial_r v=0 and the Hessian is negative semidefinite. | The viscosity term nu Ltilde v cannot create the first positive maximum in the local barrier calculation. |
| `global_concavity_blocker` | `open_blocker` | `global_concavity` | The route lacks a global theorem that partial_z^2 psi1 keeps the sign needed to make 2 u1 partial_z^2 psi1 harmless at every possible first positive maximum of v. | Without global concavity, the source derivative can be positive at an off-peak crossing and the barrier does not close. |
| `secondary_peak_blocker` | `open_blocker` | `secondary_peaks` | The route lacks an exclusion theorem for secondary axial peaks or shoulders where v may form a positive local maximum outside the locally concave primary region. | A secondary positive crossing can evade the local barrier even if the primary symmetry-center calculation is valid. |

## Control Card

- O: Worker owns only the Sprint137 axial monotonicity gate emitter and its output directory surface.
- R: Model AxialMonotonicityOfSwirlProfile for v=partial_z u1 without turning local barrier support into a global theorem.
- C: Deterministic Python emitter with rows JSON, rows CSV, summary JSON, Markdown report, validate(), and main().
- S: Symmetry, initial sign, first-crossing, differentiated source, local concavity, and diffusion sign are explicit ledger states.
- L: Local barrier rows are supported; global concavity and secondary-peak rows remain open blockers.
- P: Keep the route conditional/fail-closed and use it only as a gate inventory for later Hou-Luo analysis.
- G: Validation passes only if blockers remain open, global proof is not closed, and Clay promotion is false.
- F: Any missing required row, missing 2u1 partial_z^2 psi1 term, closed global proof, or Clay promotion fails validation.
