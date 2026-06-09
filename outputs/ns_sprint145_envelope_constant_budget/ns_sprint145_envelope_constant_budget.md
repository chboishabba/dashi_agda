# Sprint 145 Envelope Constant Budget

- Contract: `ns_sprint145_envelope_constant_budget`
- Decision: `fail_closed_no_simultaneous_envelope_constants`
- Target gate: `ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators`
- Residual inequality: `kappa_psi - C_comm * Log_BS(active_scale) - C_boundary - C_annular - C_off_peak - C_radial - C_strain >= slack_positive`
- Comparison envelope available: `False`
- Compatible simultaneous constants: `False`
- Full Clay NS solved: `False`
- Clay promotion: `False`

## Rows

### concavity_margin_kappa_psi

- Symbol: `kappa_psi`
- Status: `local_margin_only_global_constant_absent`
- Role: favorable_nonlocal_concavity_margin
- Requirement: A strict lower margin kappa_psi > 0 must dominate the total positive part of 2 u1 partial_z^2 psi1 on the complete admissible first-crossing set.
- Missing evidence: global signed-kernel dominance for partial_z^2 psi1; off-peak and annular source domination by the same kappa_psi; positive margin on every admissible r-z first crossing
- Compatible with all constants: `False`

### commutator_constant_C_comm

- Symbol: `C_comm`
- Status: `commutator_constant_absent`
- Role: radial_commutator_domination_constant
- Requirement: C_comm must bound max(-(partial_z u^r) partial_r u1, 0) on the same crossings where kappa_psi is invoked.
- Missing evidence: pointwise favorable sign theorem for the commutator; radial-gradient coupling bound for partial_r u1 at every crossing; numerical or symbolic C_comm compatible with kappa_psi after log loss
- Compatible with all constants: `False`

### biot_savart_log_factor

- Symbol: `Log_BS(active_scale)`
- Status: `log_loss_unabsorbed`
- Role: near_coincident_ring_log_multiplier
- Requirement: The envelope must absorb C_comm * Log_BS(active_scale), or prove a cancellation removing the logarithmic Biot-Savart loss.
- Missing evidence: uniform log-loss absorption constant; structural cancellation at near-coincident rings; scale relation proving kappa_psi remains positive after log amplification
- Compatible with all constants: `False`

### boundary_annular_constants

- Symbol: `C_boundary + C_annular + C_off_peak`
- Status: `boundary_annular_constants_unavailable`
- Role: boundary_annular_leakage_budget
- Requirement: Boundary, annular, and off-peak source terms must be nonpositive or strictly absorbed into the same residual budget.
- Missing evidence: boundary-compatible kernel sign cancellation theorem; annular source exclusion or domination estimate; off-peak source envelope tied to the same first-crossing set
- Compatible with all constants: `False`

### residual_slack_budget

- Symbol: `slack_positive`
- Status: `strict_residual_slack_absent`
- Role: strict_remaining_margin_after_all_losses
- Requirement: kappa_psi - C_comm * Log_BS(active_scale) - C_boundary - C_annular - C_off_peak - C_radial - C_strain >= slack_positive on every admissible first positive v crossing.
- Missing evidence: positive residual inequality after all source, commutator, log, boundary, annular, and strain losses; single scale/time/boundary normalization for every term; proof that the residual controls lower-order terms through the crossing interval
- Compatible with all constants: `False`

### simultaneous_compatibility_gate

- Symbol: `kappa_env`
- Status: `simultaneous_compatibility_unproved_fail_closed`
- Role: single_envelope_compatibility_gate
- Requirement: One theorem must choose kappa_psi, C_comm, Log_BS, boundary, annular, off-peak, strain, and slack constants on the same crossing set and prove the comparison envelope target.
- Missing evidence: ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators; simultaneous satisfiability proof for all constants; comparison scalar problem whose zero-number theorem applies; secondary peak exclusion and global axial monotonicity theorem
- Compatible with all constants: `False`

## Control Card

- O: Sprint 145 worker lane 3 owns only scripts/ns_sprint145_envelope_constant_budget.py and outputs/ns_sprint145_envelope_constant_budget/.
- R: Aggregate and normalize the constant budget required for ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators.
- C: Deterministic stdlib ledger emitting JSON summary, JSON rows, CSV, Markdown, and manifest through an atomic staging directory.
- S: kappa_psi is only locally supported; C_comm, Log_BS, boundary/annular loads, and residual slack remain simultaneously unavailable.
- L: Sprint 140 conditional constants -> Sprint 141 commutator/log hazards -> Sprint 142 nonlocal/boundary hazards -> Sprint 144 missing comparison envelope -> Sprint 145 fail-closed budget.
- P: Use this artifact as the normalized Sprint 145 constant-budget interface, not as an envelope proof.
- G: Validation passes only if all compatibility, envelope, barrier, Clay, and promotion flags remain false while the artifact is complete.
- F: Missing simultaneous theorem: ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators; no compatible residual inequality or scalar comparator exists.
