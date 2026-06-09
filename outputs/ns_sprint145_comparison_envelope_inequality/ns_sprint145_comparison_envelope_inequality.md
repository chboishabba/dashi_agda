# Sprint 145 Comparison-Envelope Inequality

- Contract: `ns_sprint145_comparison_envelope_inequality`
- Decision: `fail_closed_comparison_envelope_not_available`
- Target gate: `ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators`
- Missing coupled theorem: `CoupledAxisymmetricZeroNumberForVBarrier`
- Promotion: `hold_no_clay_promotion`

## Normalized Inequality

`Q_env(t,r,z) := 2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1 <= -kappa_env*EnvelopeControl(t,r,z) + LowerOrderAbsorbableTerms(t,r,z) on every point of AdmissibleCoupledVFirstCrossingSet`

Strict residual interface:

`kappa_local_source - C_nonlocal_source - C_radial_commutator*Log_BS(active_scale) - C_boundary_annular - C_lower_order >= slack_env > 0`

## Rows

| row_id | role | status | favorable | adverse |
|---|---|---|---:|---:|
| local_favorable_source | local_negative_source_margin_candidate | local_support_only_not_a_global_envelope | true | false |
| sign_changing_nonlocal_source | nonlocal_elliptic_source_load | sign_changing_nonlocal_source_uncontrolled | false | true |
| radial_commutator_uncontrolled | radial_transport_commutator_load | radial_commutator_positive_part_unabsorbed | false | true |
| log_loss_margin | biot_savart_log_loss_budget | log_loss_margin_not_absorbed | false | true |
| boundary_annular_constants | boundary_annular_constant_compatibility | boundary_annular_constants_absent | false | true |
| simultaneous_residual_missing | simultaneous_comparison_envelope_gate | missing_simultaneous_residual_fail_closed | false | false |

## Fail-Closed Flags

- `comparison_envelope_available`: `false`
- `comparison_envelope_proved`: `false`
- `coupled_zero_number_theorem_proved`: `false`
- `full_clay_ns_solved`: `false`
- `clay_navier_stokes_promoted`: `false`
- `artifact_complete`: `true`
- `invariants_passed`: `true`

## Control Card

- `O`: Sprint 145 worker lane 2 owns only scripts/ns_sprint145_comparison_envelope_inequality.py and outputs/ns_sprint145_comparison_envelope_inequality/.
- `R`: Normalize the desired comparison-envelope inequality for 2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1.
- `C`: Deterministic stdlib emitter producing JSON summary, JSON rows, CSV, Markdown report, and manifest with stable hashes.
- `S`: Local favorable source support exists only locally; sign-changing nonlocal source, uncontrolled radial commutator, log-loss margin, and boundary/annular constants block the simultaneous residual.
- `L`: Local source margin -> nonlocal source load -> radial/log load -> boundary/annular load -> missing Delta_env residual -> no coupled zero-number theorem.
- `P`: Emit a fail-closed obligation ledger for the next analytic proof; do not promote it to a theorem.
- `G`: Validation passes only if comparison_envelope_available/proved, coupled_zero_number_theorem_proved, full_clay_ns_solved, and clay_navier_stokes_promoted all remain false while artifact_complete is true.
- `F`: Missing ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators; without it CoupledAxisymmetricZeroNumberForVBarrier, SecondaryPeakExclusion, global axial monotonicity, and Clay promotion remain blocked.
