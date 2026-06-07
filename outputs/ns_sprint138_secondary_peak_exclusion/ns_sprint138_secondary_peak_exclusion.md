# NS Sprint 138 Secondary Peak Exclusion

- Contract: `ns_sprint138_secondary_peak_exclusion`
- Gate: `AxialMonotonicityOfSwirlProfile`
- Blocker: `SecondaryPeakExclusion`
- Sprint 138 blocker index: `2`
- Decision: `fail-closed`
- Secondary peak exclusion proved: `false`
- Blocker remains open: `true`
- Axial monotonicity gate closed: `false`
- Clay Navier-Stokes promoted: `false`

## Equations

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`
- `D_t Gamma = nu(Delta - 2 r^-1 partial_r) Gamma, so Gamma has a maximum principle, but this controls circulation amplitude rather than the one-dimensional axial peak count of u1 or v.`

## Ledger Rows

| Row | Status | Role | Observation | Obstruction | Barrier impact |
| --- | --- | --- | --- | --- | --- |
| `single_peak_initial_profile` | `assumption_recorded_not_persistent` | `initial_shape` | The contemplated Hou-Luo branch may start from a smooth single primary axial peak for u1 on the monitored half-profile, with v=partial_z u1 initially nonpositive away from the symmetry plane. | initial unimodality is not a time-propagated invariant; the coupled source and transport terms are not scalar heat flow | A first-crossing argument can start from v<=0, but it cannot exclude a later off-peak local maximum without a persistence theorem for the single-peak shape. |
| `parabolic_smoothing_support` | `support_insufficient` | `regularization` | Viscosity supplies parabolic smoothing for u1 and v, and at an interior positive maximum of v the local diffusion contribution nu Ltilde v is nonpositive. | smoothing reduces roughness but does not preserve unimodality; the differentiated equation has nonhomogeneous source and transport-gradient terms; boundary and annular localization can move the first crossing away from the primary peak | Diffusion cannot by itself create the positive maximum, but the remaining terms can still invalidate a sign contradiction at a secondary shoulder. |
| `nonlinear_source_can_form_shoulders` | `live_obstruction` | `nonlinear_shoulder_formation` | The nonlinear source ledger for v contains 2 u1 partial_z^2 psi1 plus coefficients multiplying v and transport-gradient commutators; this can concentrate growth off the primary concavity patch. | partial_z^2 psi1 is nonlocal and has no global sign theorem; off-peak positive forcing can raise shoulders before the primary maximum loses local concavity; no comparison principle orders the coupled source against a single scalar unimodal envelope | A positive shoulder can become the first positive maximum of v outside the region where the local source sign is controlled. |
| `annular_gamma_u1_constraints` | `constraint_mismatch` | `circulation_vs_swirl_profile` | The circulation Gamma obeys a maximum-principle type bound, while u1=Gamma/r^2 is the differentiated axial swirl profile used in the monotonicity gate. | Gamma control does not control axial zero counts of v; division by r^2 couples annular radial localization to the effective u1 profile; annular amplitude bounds do not prevent axial shoulders in u1 | Gamma/u1 constraints can bound amplitude in the annulus, but they do not rule out a secondary positive crossing of partial_z u1. |
| `lack_sturmian_zero_number_principle` | `missing_principle` | `zero_number_gap` | Scalar one-dimensional parabolic equations can sometimes use a Sturmian zero-number principle to prevent creation of new sign changes, but the current problem is a coupled axisymmetric system in (r,z). | no repo theorem supplies a 1D zero-number monotonicity for this coupled axisymmetric-with-swirl equation; radial dependence and nonlocal elliptic feedback break the scalar Sturmian template; source terms can create or move zeros of v | The route cannot infer preservation of the initial single sign-change pattern of v from known scalar parabolic theory. |
| `possible_secondary_positive_v_crossing` | `counter_scenario_open` | `first_crossing_failure_mode` | A secondary off-peak shoulder may cross into v>0 before any contradiction is available at the primary symmetric peak. | no boundary-free global localization of the first crossing; no exclusion of annular off-peak positive-v maxima; no theorem that the first positive crossing must occur in the locally concave primary region | This is the exact failure mode for closing AxialMonotonicityOfSwirlProfile from local barrier support. |
| `required_exclusion_theorem` | `required_not_proved` | `theorem_obligation` | A closing theorem would need to prove that, for the relevant smooth annular Hou-Luo data class, no secondary axial peak, shoulder, or positive local maximum of v can form outside the primary barrier region during the monotonicity time window. | single-peak persistence theorem absent; global sign control for partial_z^2 psi1 absent; coupled axisymmetric zero-number principle absent; annular Gamma/u1 comparison theorem absent | Until this theorem is supplied, the monotonicity gate remains open and the Hou-Luo symmetric source-sign branch remains conditional. |

## Decision

SecondaryPeakExclusion is not proved. The second Sprint 138 blocker remains open for AxialMonotonicityOfSwirlProfile, so the symmetric Hou-Luo route remains conditional and no Clay promotion is emitted.

## Control Card

- O: Worker owns only scripts/ns_sprint138_secondary_peak_exclusion.py and outputs/ns_sprint138_secondary_peak_exclusion/.
- R: Analyze SecondaryPeakExclusion as Sprint138 blocker 2 for AxialMonotonicityOfSwirlProfile and keep the decision fail-closed.
- C: Deterministic stdlib Python emitter with dataclass rows, validate(), main(), JSON, CSV, and Markdown artifacts.
- S: Single-peak initial data and parabolic smoothing are recorded, but nonlinear source terms, annular Gamma/u1 mismatch, and the absence of a coupled zero-number theorem leave secondary positive-v crossings possible.
- L: Sprint137 local barrier support -> secondary shoulder failure mode -> required exclusion theorem remains absent.
- P: Use this artifact as the fail-closed Sprint138 ledger for the secondary-peak blocker; do not use it as a proof of axial monotonicity.
- G: Validation succeeds only when SecondaryPeakExclusion is not proved, the blocker remains open, and Clay promotion is false.
- F: No Clay promotion; no closed AxialMonotonicityOfSwirlProfile; no Sturmian 1D zero-number principle is claimed for the coupled axisymmetric system.
