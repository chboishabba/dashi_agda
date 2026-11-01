# NS Sprint 139 Localized Kernel Sign Sampler

- Contract: `ns_sprint139_localized_kernel_sign_sampler`
- Blocker: `GlobalConcavityOfPsi1`
- Parent gate: `AxialMonotonicityOfSwirlProfile`
- Route decision: `fail_closed_kernel_sign_indefinite_no_promotion`
- Kernel model: `5d_radial_green_second_z_derivative_axisymmetric_S3_average`
- Local concavity supported: `true`
- Global concavity proved: `false`
- Blocker open: `true`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`

## Kernel Sign Rows

| row | region | source | weighted contribution | sign | local support | obstruction |
| --- | --- | --- | --- | --- | --- | --- |
| `local_radial_patch_same_z_support` | local_core | r'=0.82, z'=0 | -13.9745635309 | `negative_supports_concavity` | true | false |
| `local_broadened_radial_patch_support` | local_core | r'=0.62, z'=0 | -1.79103799795 | `negative_supports_concavity` | true | false |
| `local_axial_offset_same_radius_wrong_sign` | local_axial_offset | r'=1, z'=0.32 | 6.53009548138 | `positive_obstructs_concavity` | false | true |
| `nonlocal_annular_same_z_support_not_global` | nonlocal_annulus | r'=2.25, z'=0 | -0.896915771501 | `negative_supports_concavity` | false | true |
| `nonlocal_annular_axial_offset_wrong_sign` | nonlocal_annulus | r'=2.25, z'=1.65 | 0.213744860315 | `positive_obstructs_concavity` | false | true |
| `boundary_layer_near_wall_wrong_sign` | boundary_layer | r'=3, z'=2.35 | 0.106984221278 | `positive_obstructs_concavity` | false | true |
| `outer_axial_tail_wrong_sign` | outer_tail | r'=0.45, z'=1.55 | 0.0300190314897 | `positive_obstructs_concavity` | false | true |

## Interpretation

Negative weighted contributions are favorable for the local concavity direction of partial_z^2 psi1 under positive omega1. Positive rows are obstructions.  Because the sampled nonlocal annular/boundary/tail geometries include unfavorable signs, the ledger does not prove GlobalConcavityOfPsi1.

## Row Notes

- `local_radial_patch_same_z_support`: A nearby same-z radial patch gives a negative sampled second-z kernel contribution for positive omega1, matching the local concavity direction needed by the barrier source term.
- `local_broadened_radial_patch_support`: A broader same-z local radial contribution remains favorable, showing that the sampler can register local concavity support.
- `local_axial_offset_same_radius_wrong_sign`: A nearby same-radius axial offset can flip the sampled sign, so locality alone is not a signed kernel theorem.
- `nonlocal_annular_same_z_support_not_global`: An annular same-z contribution may be favorable, but this is only one geometry and cannot establish global concavity.
- `nonlocal_annular_axial_offset_wrong_sign`: An annular source displaced in z can contribute with the opposite sign, exactly the nonlocal obstruction to GlobalConcavityOfPsi1.
- `boundary_layer_near_wall_wrong_sign`: A far annular/boundary-sensitive source can have the unfavorable sign at the interior evaluation point.
- `outer_axial_tail_wrong_sign`: An outer axial tail near the axis is unfavorable, so a local Taylor concavity patch cannot control every source location.

## Control Card

- O: Worker 3 owns only scripts/ns_sprint139_localized_kernel_sign_sampler.py and outputs/ns_sprint139_localized_kernel_sign_sampler/.
- R: Sample localized axisymmetric kernel signs relevant to GlobalConcavityOfPsi1 without proving global concavity.
- C: Deterministic stdlib Python, fixed S^3 Simpson quadrature, dataclass rows, JSON, CSV, Markdown, and fail-closed validation.
- S: Same-z local radial patches support concavity, while nearby axial offsets and nonlocal annular/boundary/tail sources can produce unfavorable signs.
- L: Ltilde-as-5d-radial Green kernel -> second-z derivative -> localized S^3 average -> sign classification -> route decision.
- P: Keep GlobalConcavityOfPsi1 open; use the sampler only as a ledger of support and obstructions.
- G: Validation requires at least one local support row, at least one positive nonlocal obstruction, no global proof, no full Clay NS solved flag, and no promotion.
- F: Missing required rows, no positive obstruction, any global concavity proof claim, or any Clay promotion fails closed.
