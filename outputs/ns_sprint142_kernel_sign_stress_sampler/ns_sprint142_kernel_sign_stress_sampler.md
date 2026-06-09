# NS Sprint 142 Kernel Sign Stress Sampler

- Contract: `ns_sprint142_kernel_sign_stress_sampler`
- Parent ledger: `ns_sprint139_localized_kernel_sign_sampler`
- Blocker: `GlobalNegativeKernelSignForPartialZ2Psi1`
- Route decision: `fail_closed_no_uniform_global_negative_sign_theorem`
- Has favorable rows: `true`
- Has adverse rows: `true`
- Global concavity proved: `false`
- Uniform global negative sign theorem proved: `false`
- Clay Navier-Stokes promoted: `false`

## Rows

| row | geometry | source | weight | contribution | sign | favorable | adverse |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `favorable_local_same_z_inner_radial_patch` | `favorable_local_same_z` | r'=0.84, z'=0 | 1 | -18.493235685 | `negative_favorable_for_local_concavity` | true | false |
| `favorable_local_same_z_outer_radial_patch` | `favorable_local_same_z` | r'=1.22, z'=0 | 1 | -16.9743615606 | `negative_favorable_for_local_concavity` | true | false |
| `adverse_axial_offset_same_radius` | `adverse_axial_offset` | r'=1, z'=0.34 | 1 | 5.80429638916 | `positive_adverse_to_negative_sign_theorem` | false | true |
| `adverse_annular_source_axial_offset` | `adverse_annular_source` | r'=2.1, z'=1.55 | 1 | 0.254630847241 | `positive_adverse_to_negative_sign_theorem` | false | true |
| `adverse_boundary_image_reflection` | `adverse_boundary_image` | r'=1.35, z'=-0.82 | -0.65 | -0.505237196421 | `negative_favorable_for_local_concavity` | false | true |
| `adverse_far_tail_axial_column` | `adverse_far_tail` | r'=0.52, z'=2.35 | 1 | 0.0113395544972 | `positive_adverse_to_negative_sign_theorem` | false | true |

## Conclusion

The stress sampler preserves localized same-z negative-sign support, but axial-offset, annular, boundary-image, and far-tail rows keep the sign ledger mixed.  Therefore it concludes no uniform global negative sign theorem for partial_z^2 psi1.

## Row Notes

- `favorable_local_same_z_inner_radial_patch`: Same-z local radial separation gives a negative partial_z^2 kernel sample, preserving the Sprint 139 localized support.
- `favorable_local_same_z_outer_radial_patch`: A second same-z local row remains favorable, so the sampler does not erase useful localized-kernel evidence.
- `adverse_axial_offset_same_radius`: Axial offset can flip the sampled sign, blocking a theorem based only on local radial intuition.
- `adverse_annular_source_axial_offset`: An annular source away from the local patch has the wrong sign, so same-z favorable samples cannot globalize.
- `adverse_boundary_image_reflection`: A boundary-image contribution changes the signed balance; the sampler records it as a boundary-sensitive obstruction.
- `adverse_far_tail_axial_column`: A far-tail axial column remains sign-adverse at the interior evaluation point, keeping the global kernel theorem open.

## Control Card

- O: Sprint 142 lane 3 writes only scripts/ns_sprint142_kernel_sign_stress_sampler.py and outputs/ns_sprint142_kernel_sign_stress_sampler/.
- R: Stress sample partial_z^2 psi1 kernel signs with favorable same-z rows plus axial, annular, boundary-image, and far-tail adverse rows.
- C: Pure Python stdlib, deterministic S^3 Simpson quadrature, JSON summary, JSON rows, CSV, Markdown, fail-closed validation.
- S: Local same-z radial rows are favorable, but adverse/nonlocal geometries keep the global sign theorem open.
- L: 5d radial Green kernel -> partial_z^2 derivative -> angular average -> radial measure weighting -> sign stress ledger.
- P: Conclude no uniform global negative sign theorem; retain only localized support evidence.
- G: Validation requires has_favorable_rows=true, has_adverse_rows=true, global_concavity_proved=false, uniform theorem false, and no Clay promotion.
- F: Missing required rows/classes, absent favorable/adverse rows, any global proof claim, or any promotion fails closed.
