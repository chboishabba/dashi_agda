# ns_sprint144_coupled_zero_number_interface

## Decision

- Decision: `fail_closed_coupled_zero_number_interface_not_satisfied`
- Target gate: `SecondaryPeakExclusionForVBarrier`
- Target variable: `v = partial_z u1`
- Theorem interface: `CoupledAxisymmetricZeroNumberForVBarrier`
- Coupled zero-number theorem proved: `False`
- Scalar transfer valid: `False`
- Secondary peak exclusion proved: `False`
- Global barrier closed: `False`
- Full Clay NS solved: `False`
- Clay promotion: `False`
- Artifact complete: `True`
- Invariants passed: `True`

## Interface

- Scalar template: one-dimensional scalar parabolic zero-number theorem on a fixed interval with closed local operator, admissible boundary data, regular coefficients, and no sign-indefinite external source capable of creating new zeros
- Coupled operator: `Ltilde = partial_r^2 + 3/r partial_r + partial_z^2`
- u1 equation: `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- v equation: `D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 - (partial_z u^z) v`

## Normalized Rows

| row_id | layer | status | hypotheses needed | required constants | consequence |
| --- | --- | --- | --- | --- | --- |
| scalar_template_valid_only_1d | scalar_template | scalar_template_not_transferable | identify an admissible one-dimensional comparison variable; prove the v dynamics restrict to a closed scalar equation on that variable; show all source, transport, and boundary terms satisfy scalar theorem assumptions | coefficient regularity margin for the scalar template; boundary compatibility margin for the comparison interval | The scalar zero-number theorem cannot be used directly for secondary peak exclusion. |
| coupled_rz_operator_gap | coupled_operator | coupled_rz_operator_unmatched | dimension-reduction theorem from r-z crossings to axial zero counts; control of radial jets at every admissible v-barrier crossing; maximum-principle compatibility for the coupled r-z operator | radial diffusion domination margin; axis/annulus regularity constants for 3/r partial_r; r-z localization constants compatible with the barrier scale | The coupled operator gap leaves the theorem interface open. |
| nonlocal_source_gap | nonlocal_source | nonlocal_source_uncontrolled | sign or domination theorem for partial_z^2 psi1 in the barrier region; nonlocal feedback bound that cannot create secondary positive peaks; compatibility between elliptic estimates and zero-number decay | global psi1 second-axial-derivative bound; u1-weighted nonlocal source absorption margin; off-peak shoulder suppression constant | The nonlocal source term blocks scalar zero-number transfer. |
| commutator_transport_gap | transport_commutator | commutator_transport_open | radial-gradient coupling control for partial_r u1; nonlocal velocity-gradient bounds for partial_z u^r and partial_z u^z; commutator domination inequality at first positive v crossings | partial_z u^r times partial_r u1 absorption constant; velocity-gradient reaction bound; transport commutator margin compatible with the global barrier | The theorem interface cannot close without commutator transport constants. |
| moving_boundary_annular_gap | domain_geometry | moving_annular_domain_open | zero-number theorem on moving annular comparison domains; boundary jet compatibility for the axisymmetric r-z barrier; proof that localization changes do not reset or hide zero counts | annular boundary trace constant; moving-window speed and curvature margin; boundary layer absorption constant | Moving boundary and annular regimes remain outside the normalized interface. |
| constants_compatibility_gap | quantitative_constants | constants_not_compatible | single constants ledger spanning all theorem assumptions; monotone implication from theorem constants to secondary peak exclusion; compatibility proof with existing global barrier constants | operator gap constant; nonlocal source constant; commutator transport constant; moving annular boundary constant; global barrier closure margin | The interface cannot be consumed by the global v-barrier route. |
| theorem_absent | required_theorem | required_theorem_absent | CoupledAxisymmetricZeroNumberForVBarrier; proof that scalar transfer is valid for the coupled v equation; proof that the theorem excludes secondary positive v peaks; proof that the resulting exclusion closes the global barrier | complete theorem constants tuple; constants compatibility certificate; promotion-safe global barrier margin | The artifact stays fail-closed with no Clay Navier-Stokes promotion. |

## Control Card

- O: Worker lane 2 owns only scripts/ns_sprint144_coupled_zero_number_interface.py and outputs/ns_sprint144_coupled_zero_number_interface/.
- R: Normalize the missing theorem interface for CoupledAxisymmetricZeroNumberForVBarrier.
- C: Deterministic Python emitter producing summary JSON, row JSON, CSV, Markdown, and a manifest through a temporary output directory.
- S: All rows keep the coupled theorem unproved, scalar transfer invalid, secondary peak exclusion unproved, and the global barrier open.
- L: Scalar 1D template -> coupled r-z operator gap -> nonlocal source gap -> commutator transport gap -> moving annular gap -> constants gap -> absent theorem.
- P: Use this as an interface ledger only; do not treat it as a theorem, secondary peak exclusion proof, barrier closure, or Clay promotion.
- G: Validation passes only if required rows are exact and all proof, transfer, closure, and promotion booleans stay false.
- F: Missing theorem interface: CoupledAxisymmetricZeroNumberForVBarrier; no scalar transfer, no secondary peak exclusion, no global barrier closure, no full Clay Navier-Stokes solution, and no Clay promotion.

## Governance

This artifact is fail-closed. It normalizes the missing coupled zero-number theorem interface and does not close scalar transfer, secondary peak exclusion, the global barrier, or Clay Navier-Stokes.
