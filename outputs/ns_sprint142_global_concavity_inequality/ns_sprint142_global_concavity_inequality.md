# NS Sprint 142 Global Concavity Inequality

- Contract: `ns_sprint142_global_concavity_inequality`
- Gate: `GlobalConcavityOfPsi1`
- Decision: `fail_closed_missing_global_concavity_inequality`
- Target inequality: `partial_z^2 psi1(t,r,z) <= -kappa_concavity for every (t,r,z) in AdmissibleVBarrierCrossingSet`
- Required theorem: `SimultaneousGlobalConcavityOfPsi1OnAdmissibleVBarrierCrossingSet`
- Same Sprint 140 constants: `true`
- Global concavity proved: `false`
- Global barrier closed: `false`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`

## Sprint 140 Constant Interface

- `active_scale`: `active_scale_shared_with_sprint140`
- `crossing_set`: `AdmissibleVBarrierCrossingSet`
- `time_window`: `T_barrier_shared_with_sprint140`
- `boundary_regime`: `axis_annulus_boundary_regime_shared_with_sprint140`
- `concavity_margin`: `kappa_concavity`
- `commutator_margin`: `kappa_comm`
- `diffusion_margin`: `kappa_diffusion`
- `strain_budget`: `C_strain`
- `log_loss`: `Log_BS(active_scale)`
- `slack`: `strict_positive_slack`

## Rows

| Row | Role | Symbol | Status | Required bound | Missing evidence |
| --- | --- | --- | --- | --- | --- |
| `local_taylor_concavity_margin` | `local_center_margin_candidate` | `kappa_local` | `local_margin_available_only_conditionally` | The local Taylor expansion must produce partial_z^2 psi1 <= -kappa_concavity on every admissible first positive v crossing, not only near the primary center. | uniform radius covering the full admissible crossing set; lower bound kappa_local >= kappa_concavity on the Sprint 140 scale; exclusion of off-center first positive v crossings outside the local patch |
| `elliptic_nonlocal_source_contribution` | `elliptic_nonlocal_source_budget` | `N_elliptic` | `nonlocal_source_sign_open` | Every nonlocal omega1 contribution to partial_z^2 psi1 must be dominated so the total elliptic reconstruction preserves partial_z^2 psi1 <= -kappa_concavity on the active crossing set. | signed elliptic kernel dominance theorem; quantitative bound for remote omega1 contributions on the Sprint 140 scale; proof that nonlocal positive contributions cannot erase kappa_concavity |
| `annular_boundary_contribution` | `annular_boundary_compatibility` | `B_annular` | `annular_boundary_budget_open` | Annular and boundary contributions must be nonpositive or absorbed into the same kappa_concavity budget at every admissible v-barrier crossing. | boundary-compatible comparison theorem for partial_z^2 psi1; annular contribution exclusion or domination estimate; shared axis/boundary regime for concavity, commutator, and diffusion budgets |
| `tail_persistence_window` | `tail_and_time_window_persistence` | `P_tail(T_barrier)` | `tail_persistence_open` | The strict inequality partial_z^2 psi1 <= -kappa_concavity must persist throughout the Sprint 140 barrier time window, including remote tail effects before the first v crossing. | transport-stable concavity invariant through T_barrier; tail estimate compatible with the same active scale and boundary regime; proof no delayed source rearrangement destroys the margin before crossing |
| `missing_simultaneous_concavity_theorem` | `simultaneous_global_concavity_gate` | `Delta_concavity = -partial_z^2 psi1 - kappa_concavity` | `missing_required_theorem_fail_closed` | A single theorem must prove Delta_concavity >= 0 using the same scale, time window, crossing set, and boundary constants as Sprint 140. | SimultaneousGlobalConcavityOfPsi1OnAdmissibleVBarrierCrossingSet; one crossing-set theorem shared by local Taylor, elliptic source, annular boundary, and persistence controls; strict positive kappa_concavity compatible with Sprint 140 constants; global barrier theorem separated from local conditional bookkeeping |

## Control Card

- O: Sprint 142 lane 2 owns only scripts/ns_sprint142_global_concavity_inequality.py and outputs/ns_sprint142_global_concavity_inequality/.
- R: Normalize the inequality partial_z^2 psi1 <= -kappa_concavity on the entire admissible v-barrier crossing set.
- C: Deterministic stdlib Python emitter producing JSON summary, JSON rows, CSV, and Markdown with stable SHA-256 row hashes.
- S: Rows cover local Taylor concavity margin, elliptic nonlocal source contribution, annular/boundary contribution, tail/persistence window, and the missing simultaneous concavity theorem.
- L: Use the same Sprint 140 active scale, crossing set, time window, boundary regime, and kappa_concavity interface for every row.
- P: Treat the artifact as the next analytic obligation ledger before any GlobalConcavityOfPsi1 closure or barrier promotion.
- G: Validation passes only while global_concavity_proved, global_barrier_closed, full_clay_ns_solved, and clay_navier_stokes_promoted remain false.
- F: Missing rows, mismatched Sprint 140 constants, accidental theorem/proof closure, global barrier closure, full Clay NS solve, or Clay promotion fails validation.
