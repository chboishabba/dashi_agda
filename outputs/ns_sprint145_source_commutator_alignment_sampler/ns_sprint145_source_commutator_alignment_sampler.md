# Sprint 145 Source/Commutator Alignment Sampler

This artifact is a deterministic fail-closed sampler for the Sprint 145 comparison-envelope gate.

## Decision

- decision: `fail_closed_alignment_sampler_no_global_theorem`
- missing theorem: `GlobalSourceCommutatorAlignmentForVBarrier`
- missing envelope: `ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators`
- global alignment theorem proved: `false`
- comparison envelope available: `false`
- full Clay NS solved: `false`
- Clay promotion: `false`

## Rows

| row_id | geometry | source | commutator | residual | class |
|---|---:|---:|---:|---:|---|
| local_core_cancellation_support | local_core | -0.84 | -0.1296 | -0.9696 | favorable_same_sign_damping_cancellation_support |
| local_log_bounded_cancellation_support | local_log_bounded | -0.5332 | -0.088 | -0.6212 | favorable_same_sign_damping_cancellation_support |
| off_peak_reinforcement_positive_source | off_peak | 0.5772 | 0.13804 | 0.71524 | adverse_same_sign_growth_reinforcement |
| annular_grazing_reinforcement | annular | 0.3672 | 0.52164 | 0.88884 | adverse_same_sign_growth_reinforcement |
| boundary_image_reinforcement | boundary | 0.2394 | 0.304565 | 0.543965 | adverse_same_sign_growth_reinforcement |
| mixed_annular_cancellation_not_uniform | annular | -0.2304 | 0.114 | -0.1164 | mixed_cancellation_damping_but_not_uniform |
| tail_commutator_reinforcement | tail | 0.1344 | 0.27993 | 0.41433 | adverse_same_sign_growth_reinforcement |

## Control Card

- O: Worker lane 4 owns only scripts/ns_sprint145_source_commutator_alignment_sampler.py and outputs/ns_sprint145_source_commutator_alignment_sampler/.
- R: Classify favorable cancellation and adverse reinforcement for 2*u1*partial_z^2 psi1 versus -(partial_z u^r)*partial_r u1.
- C: Deterministic Python sampler emitting summary JSON, row JSON, CSV, Markdown, and manifest through an atomic staging directory.
- S: Local rows can damp, but off-peak, annular, boundary, and tail rows produce or preserve positive residuals.
- L: Source proxy + radial commutator proxy -> combined residual -> alignment class -> fail-closed envelope obstruction ledger.
- P: Use this as evidence that local cancellation is not a global alignment theorem and does not construct the Sprint 145 envelope.
- G: Validation passes only if favorable and adverse rows exist while all theorem, envelope, barrier, Clay, and promotion flags remain false.
- F: Missing: GlobalSourceCommutatorAlignmentForVBarrier and ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators; no global axial monotonicity or Clay promotion follows.
