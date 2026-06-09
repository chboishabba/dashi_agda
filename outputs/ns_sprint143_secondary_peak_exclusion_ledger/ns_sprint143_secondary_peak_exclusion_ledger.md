# Sprint 143 Secondary Peak Exclusion Ledger

- Contract: `ns_sprint143_secondary_peak_exclusion_ledger`
- Program: `HouLuoAxisymmetricWithSwirlBarrierProgram`
- Parent gate: `AxialMonotonicityOfSwirlProfile`
- Blocker: `SecondaryPeakExclusion`
- Decision: `fail_closed_secondary_peak_exclusion_ledger_open`
- Normalized theorem needed: `No secondary axial peak, shoulder, or off-route positive local maximum of v=partial_z u1 forms on the monitored interval.`
- Secondary peak exclusion proved: `false`
- Secondary peak exclusion closed: `false`
- Global barrier closed: `false`
- Global proof: `false`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Artifact complete: `true`
- Invariants passed: `true`
- Rows hash: `654e54ba5c031d8da20639d2f305b9c5f7c13527c1379da16d358afd3f4a3d1d`

## Rows

| row_id | status | role | support | obstruction | required input |
| --- | --- | --- | --- | --- | --- |
| initial_single_peak_support | support_recorded_not_persistent | initial_shape_support | Sprint 138 single-peak initial profile row; smooth classical initial data; initial sign pattern v<=0 away from the symmetry-center peak | initial single-peak shape is not a propagated invariant; the v equation is coupled and nonhomogeneous rather than scalar heat flow; no time-persistence theorem keeps the first crossing on the primary route | single-peak persistence theorem over the monitored interval; proof that all first positive v maxima remain on the primary axial route |
| symmetry_support | support_recorded_local_only | symmetry_axis_support | Hou-Luo symmetric branch bookkeeping; center-plane parity constraints; primary local barrier region from earlier axial monotonicity ledgers | symmetry at the primary center does not order the full monitored interval; symmetric pairs of off-center shoulders are still compatible with parity; off-route local maxima can appear without violating center-plane symmetry | symmetry-to-global-unimodality theorem; proof excluding symmetric off-center shoulder pairs for v |
| parabolic_smoothing_insufficiency | support_insufficient | regularization_limit | viscous term nu Ltilde v; classical smoothing for positive viscosity; nonpositive diffusion sign at an interior positive maximum | smoothing does not preserve unimodality in the coupled equation; source and transport-gradient terms can offset diffusion; boundary and annular localization can move the relevant maximum | comparison principle adapted to the full v equation; strict residual inequality after source, transport, boundary, and annular terms |
| nonlinear_source_shoulder | open_failure_mode | nonlinear_shoulder_failure_mode | D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v; Sprint 138 nonlinear shoulder row; Sprint 140 constant ledger requires a secondary exclusion radius/window | 2 u1 partial_z^2 psi1 is not globally signed on the monitored interval; transport-gradient terms can reinforce off-route growth; local concavity support does not cover every possible first positive maximum | global sign, domination, or cancellation theorem for the active nonlinear source; proof that nonlinear forcing cannot create a secondary shoulder of v |
| boundary_annular_migration | open_boundary_annular_hazard | off_route_migration_failure_mode | Sprint 142 boundary/annulus concavity ledger; annular Hou-Luo scaling window; Gamma maximum-principle amplitude support | Gamma amplitude control does not control axial zero counts of v; boundary-compatible elliptic effects can change the active source sign; annular shoulders can sit outside the local primary route | boundary-compatible secondary-peak exclusion theorem; annular migration exclusion or signed-kernel domination theorem; proof that the monitored interval stays inside one common barrier window |
| missing_coupled_zero_number_theorem | missing_theorem | zero_number_gap | scalar one-dimensional parabolic zero-number theory is a known template; v is the axial derivative of u1 | the equation is axisymmetric in (r,z) and coupled through psi1; nonlocal elliptic feedback is outside scalar Sturmian theory; source terms can create or move zeros of v | coupled axisymmetric zero-number or shape-persistence theorem; formal bridge from that theorem to no secondary positive local maximum of v |
| missing_constants | missing_constants | constant_gap | Sprint 140 constant compatibility ledger names the required windows; secondary-peak exclusion radius/window is an explicit assembly input | no scale-uniform exclusion radius is supplied; no monitored time window is matched to concavity and commutator constants; no strict combined inequality closes all source, diffusion, strain, boundary, and annular terms | R_excl and T_excl for the monitored interval; quantitative margin budget compatible with all barrier ledgers; source, boundary, annular, diffusion, strain, and commutator constants on one crossing set |

## Decision

The ledger does not prove SecondaryPeakExclusion. The normalized theorem remains a required input before the axial barrier can close, so no global proof or Clay promotion is emitted.

## Control Card

- O: Worker lane 2 owns only scripts/ns_sprint143_secondary_peak_exclusion_ledger.py and outputs/ns_sprint143_secondary_peak_exclusion_ledger/.
- R: Normalize the theorem still needed: no secondary axial peak, shoulder, or off-route positive local maximum of v on the monitored interval.
- C: Stdlib Python deterministic emitter with dataclass rows, stable SHA-256 hashes, validation, JSON, CSV, and Markdown.
- S: Initial peak and symmetry support exist only locally; smoothing, nonlinear source terms, boundary/annular migration, missing zero-number theory, and missing constants keep the blocker open.
- L: Sprint 138 secondary-peak blocker plus Sprint 140/142 ledgers imply a normalized theorem obligation, not a proof.
- P: Use the artifact as a fail-closed ledger for future theorem work; do not use it as a global barrier certificate.
- G: Validation passes only when secondary-peak exclusion, global barrier, global proof, Clay solution, and promotion flags are false.
- F: Any missing required row, claimed theorem closure, hidden global barrier closure, missing constants closure, or promotion fails validation.
